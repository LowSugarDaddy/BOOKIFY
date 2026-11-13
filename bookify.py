#!/usr/bin/env python3
"""bookify - turn a web page or a text file into a book-style PDF (trade paperback).

  extract SRC [-o book.md]      URL or file (html, txt, md, docx, odt, epub, rtf, pdf)
                                -> book.md (YAML header + light markdown) + outline
  outline book.md               headings / candidate headings with line numbers
  fix     book.md --promote RX --with-title | --join | --shift N   structural edits (no need to read the text)
  build   book.md [-o out.pdf]  typeset with XeLaTeX, then verify + contact sheet
  verify  book.md out.pdf       word-by-word check: every word of book.md is in the PDF
  preview out.pdf [--pages 3,9] contact sheet (all pages) or chosen pages as PNG

Run `bookify.py spec` for the markup of book.md.
Needs: python3 (bs4, yaml, pypdf, PIL), pandoc >= 2.17, xelatex, poppler-utils.
"""
import argparse, datetime, glob, json, os, re, shutil, subprocess, sys, tempfile
import unicodedata, urllib.request, difflib

SPEC = r"""
book.md = YAML header + pandoc markdown. One paragraph per line is fine.

YAML keys (only title is required):
  title, subtitle, author, translator, editor
  original:  "London: Moses Pitt, 1671"   (imprint of the original edition)
  source:    URL or description of the source
  lang:      en | pl | de | fr | la | it | es | nl | cs ...   (hyphenation, quotes)
  trim:      6x9 (default) | 5.5x8.5 | 5x8 | a5
  font:      "TeX Gyre Pagella" (default) | "TeX Gyre Termes" | "TeX Gyre Bonum" ...
  fontsize:  10.5 (default)
  running-title: short title for even-page heads
  toc: true   toc-depth: 1 (chapters) | 2 (+ sections)
  dropcaps: true   half-title: true
  license:   e.g. "The text is in the public domain."
  colophon:  extra paragraph(s) for the colophon page (markdown allowed)
  edition:   e.g. "Digital edition, 2026"  (default: "Digital edition, <year>")
  output:    file name of the PDF

Body:
  # Label | Title | Subtitle        chapter: new page, centred head, drop cap
        e.g.  # Chap. II. | Of the first Tincture   /   # Chapter 1   /   # | Preface
  # ... {.part}                     part/work opener on a recto page, text follows
  # ... {.part .alone}              part title alone on its own recto page
  # ... {.continue}                 chapter head without a page break
  # ... {.nodrop}                   no drop cap;   {toc="Short"}  {running="Head"}
  ## Section                        centred letter-spaced heading (in TOC if toc-depth 2)
  ### Subheading                    small centred italic heading
  *italic*  **bold**  [Small Caps]{.smallcaps}   footnote^[text]
  | verse line                      line block = poem (blank "|" line = stanza break)
  > quotation                       block quote
  * * *                             scene break (asterisks)
  ::: {.titlepage}  ... :::         facsimile title page: inside, # ## ### #### set
                                    sizes (large..small spaced), # X {.huge} = 28pt,
                                    paragraphs = imprint,
                                    * * * = vertical fill. The FIRST one replaces the
                                    automatic title page; later ones stay where they are.
  ::: {.note} ... :::               small centred italic (editor's/transcriber's note)
  ::: {.center} / {.right} / {.closing} / {.finis} / {.epigraph} ... :::
  ::: {.pagebreak}
  :::
"""

HERE = os.path.dirname(os.path.abspath(__file__))
UA = 'Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124 Safari/537.36'
MD_READER = 'markdown-raw_tex-raw_html-citations-tex_math_dollars-subscript-superscript-auto_identifiers-implicit_figures'


def die(msg):
    print('ERROR: ' + msg, file=sys.stderr)
    sys.exit(1)


def run(cmd, **kw):
    return subprocess.run(cmd, capture_output=True, text=True, **kw)


# ============================================================================
#  EXTRACT
# ============================================================================
def esc_md(s, underscores=True):
    s = s.replace('\\', '\\\\')
    for c in '*`[]<$~^':
        s = s.replace(c, '\\' + c)
    if underscores:
        s = s.replace('_', '\\_')
    return s


def esc_block_start(s):
    """protect a paragraph that would otherwise start a list/heading/quote"""
    s = re.sub(r'^(\s*)([#>|:+\-])', r'\1\\\2', s)
    s = re.sub(r'^(\s*)(\d+|[A-Za-z]|[ivxlcdmIVXLCDM]+)([.)])(\s)', r'\1\2\\\3\4', s)
    s = re.sub(r'^(\s*)\(([A-Za-z0-9]+)\)(\s)', r'\1\\(\2)\3', s)
    return s


def wrap(mark, s):
    if not s.strip():
        return s
    lead = s[:len(s) - len(s.lstrip())]
    trail = s[len(s.rstrip()):]
    return lead + mark + s.strip() + mark + trail


def wrap_sc(s):
    if not s.strip():
        return s
    lead = s[:len(s) - len(s.lstrip())]
    trail = s[len(s.rstrip()):]
    return lead + '[' + s.strip() + ']{.smallcaps}' + trail


SC_CLASSES = {'smcap', 'smallcaps', 'small-caps', 'sc', 'smcp', 'caps'}
JUNK_CLASS = re.compile(r'editsection|noprint|navbox|printfooter|catlinks|mw-jump|^toc$|sharedaddy|share|comment|breadcrumb|cookie|advert|sidebar|related', re.I)


def html_inline(node):
    return inline_list(node.children)


def inline_list(nodes):
    from bs4 import NavigableString, Comment
    out = []
    for ch in nodes:
        if isinstance(ch, Comment):
            continue
        if isinstance(ch, NavigableString):
            out.append(esc_md(re.sub(r'\s+', ' ', str(ch))))
            continue
        n = ch.name
        cl = set(c.lower() for c in ch.get('class', []))
        st = (ch.get('style') or '').lower()
        if n in ('i', 'em', 'cite', 'var', 'dfn'):
            out.append(wrap('*', html_inline(ch)))
        elif n in ('b', 'strong'):
            out.append(wrap('**', html_inline(ch)))
        elif n == 'br':
            out.append('\x00BR\x00')
        elif n in ('img', 'script', 'style', 'svg', 'button'):
            continue
        elif (cl & SC_CLASSES) or 'small-caps' in st:
            out.append(wrap_sc(html_inline(ch)))
        else:
            out.append(html_inline(ch))
    return ''.join(out)


def clean_inline(s):
    s = re.sub(r'[ \t]+', ' ', s)
    return s.strip()


HEAD = {'h1', 'h2', 'h3', 'h4', 'h5', 'h6'}
BLOCKISH = HEAD | {'p', 'div', 'section', 'article', 'main', 'center', 'blockquote', 'ul', 'ol',
                   'li', 'pre', 'table', 'tr', 'td', 'th', 'tbody', 'thead', 'hr', 'figure', 'dl',
                   'dt', 'dd', 'header', 'footer', 'aside', 'nav', 'form', 'body', 'span', 'font'}


def has_block_children(el):
    from bs4 import Tag
    return any(isinstance(c, Tag) and c.name in BLOCKISH - {'span', 'font'} for c in el.children)


def split_lines(el):
    """inline content of el split at <br> -> list of lines"""
    s = html_inline(el)
    return [clean_inline(x) for x in s.split('\x00BR\x00')]


def html_blocks(el, out, stats):
    """append ('h',lvl,text) ('p',text) ('lines',[..]) ('hr',) ('div',cls,[blocks]) ('quote',[blocks])"""
    from bs4 import NavigableString, Tag, Comment
    buf = []

    def flush():
        if buf:
            txt = clean_inline(''.join(buf).replace('\x00BR\x00', ' '))
            if txt:
                out.append(('p', txt))
            buf.clear()

    for ch in el.children:
        if isinstance(ch, Comment):
            continue
        if isinstance(ch, NavigableString):
            if str(ch).strip():
                buf.append(esc_md(re.sub(r'\s+', ' ', str(ch))))
            continue
        if not isinstance(ch, Tag):
            continue
        n = ch.name
        cl = ' '.join(ch.get('class', [])).lower()
        if n in ('script', 'style', 'noscript', 'nav', 'form', 'button', 'aside', 'iframe', 'svg',
                 'select', 'input', 'textarea') or (cl and JUNK_CLASS.search(cl)):
            continue
        if n == 'img':
            stats['images'] += 1
            continue
        if n not in BLOCKISH or (n in ('span', 'font') and not has_block_children(ch)):
            buf.append(inline_list([ch]))
            continue
        flush()
        if n in HEAD:
            txt = clean_inline(html_inline(ch).replace('\x00BR\x00', ' '))
            if txt:
                lvl = int(n[1])
                if 'h1' in cl.split() or n == 'h1':
                    txt += ' {.huge}'
                out.append(('h', lvl, txt))
        elif n == 'p':
            if 'poem' in cl or 'verse' in cl:
                out.append(('lines', split_lines(ch)))
                continue
            lines = split_lines(ch)
            if len(lines) >= 3 and max(len(x) for x in lines) < 90:
                out.append(('lines', lines))
            else:
                txt = clean_inline(' \\\n'.join(x for x in lines if x))
                if txt:
                    if 'center' in cl:
                        out.append(('div', 'center', [('p', txt)]))
                    else:
                        out.append(('p', txt))
        elif n == 'hr':
            out.append(('hr',))
        elif n == 'blockquote':
            sub = []
            html_blocks(ch, sub, stats)
            out.append(('quote', sub))
        elif n in ('ul', 'ol'):
            for k, li in enumerate(ch.find_all('li', recursive=False)):
                txt = clean_inline(html_inline(li).replace('\x00BR\x00', ' '))
                if txt:
                    out.append(('p', ('- ' if n == 'ul' else '%d. ' % (k + 1)) + txt, 'list'))
        elif n == 'pre':
            out.append(('lines', [esc_md(x) for x in ch.get_text().split('\n')]))
        elif n == 'table':
            for tr in ch.find_all('tr'):
                cells = [clean_inline(html_inline(td).replace('\x00BR\x00', ' ')) for td in tr.find_all(['td', 'th'])]
                cells = [c for c in cells if c]
                if cells:
                    out.append(('p', ' — '.join(cells)))
        elif ('poem' in cl or 'verse' in cl or 'stanza' in cl) and n in ('div', 'section'):
            lines = []
            stanzas = ch.find_all(class_=re.compile('stanza')) or [ch]
            for si, stz in enumerate(stanzas):
                if si:
                    lines.append('')
                leafs = stz.find_all(['span', 'div', 'p'], recursive=False)
                if leafs and all(not l.find_all(['span', 'div', 'p']) or True for l in leafs) and len(leafs) > 1:
                    for l in leafs:
                        t = clean_inline(html_inline(l).replace('\x00BR\x00', ''))
                        if t:
                            lines.append(t)
                else:
                    lines.extend(x for x in split_lines(stz) if x)
            out.append(('lines', lines))
        elif n == 'center':
            sub = []
            html_blocks(ch, sub, stats)
            nh = sum(1 for b in sub if b[0] == 'h')
            out.append(('div', 'titlepage' if nh >= 3 else 'center', sub))
        else:
            html_blocks(ch, out, stats)
    flush()


def pick_main(soup):
    """deepest element that still holds >= 85% of the long-paragraph text"""
    for t in soup(['script', 'style', 'noscript', 'nav', 'form', 'iframe', 'svg']):
        t.decompose()
    body = soup.body or soup
    def weight(el):
        return sum(len(p.get_text()) for p in el.find_all(['p', 'div', 'td'])
                   if len(p.get_text()) > 200 and not p.find(['p', 'div', 'td']))
    total = weight(body)
    if total == 0:
        return body
    node = body
    while True:
        best = None
        for ch in node.find_all(recursive=False):
            if weight(ch) >= 0.85 * total:
                best = ch
                break
        if best is None:
            return node
        node = best


def blocks_to_md(blocks, minlvl, inside_tp=False):
    out = []
    prev = None
    for k, b in enumerate(blocks):
        kind = b[0]
        if kind == 'h':
            lvl = b[1]
            if inside_tp:
                lvl = max(1, min(4, lvl - 1))
            else:
                lvl = max(1, min(3, lvl - minlvl + 1))
            t = b[2].rstrip('#').strip()
            if not inside_tp:
                t = t.replace(' {.huge}', '')
            out.append('#' * lvl + ' ' + t.replace('|', '\\|'))
        elif kind == 'p':
            if len(b) > 2 and b[2] == 'list':
                out.append(b[1])
            else:
                out.append(esc_block_start(b[1]))
        elif kind == 'lines':
            ls = list(b[1])
            while ls and not ls[-1]:
                ls.pop()
            while ls and not ls[0]:
                ls.pop(0)
            if ls:
                out.append('\n'.join(('| ' + x) if x else '|' for x in ls))
        elif kind == 'hr':
            nxt = blocks[k + 1] if k + 1 < len(blocks) else None
            if inside_tp:
                out.append('* * *')
            elif nxt is not None and nxt[0] not in ('h', 'hr') and prev not in (None, 'hr') and not (nxt[0] == 'div' and nxt[1] == 'titlepage'):
                out.append('* * *')
        elif kind == 'quote':
            inner = blocks_to_md(b[1], minlvl)
            out.append('\n'.join('> ' + l if l else '>' for l in inner.split('\n')))
        elif kind == 'div' and inside_tp:
            out.append(blocks_to_md(b[2], minlvl, inside_tp=True))
        elif kind == 'div':
            inner = blocks_to_md(b[2], minlvl, inside_tp=(b[1] == 'titlepage'))
            out.append('::: {.%s}\n%s\n:::' % (b[1], inner))
        prev = kind
    return '\n\n'.join(x for x in out if x.strip())


def html_to_md(html, stats):
    from bs4 import BeautifulSoup
    soup = BeautifulSoup(html, 'html.parser')
    meta = {}
    t = soup.find('meta', attrs={'property': 'og:title'})
    title = (t.get('content') if t else None) or (soup.title.get_text() if soup.title else '')
    title = re.split(r'\s+[|–—]\s+', title.strip())[0] if title else ''
    if title:
        meta['title'] = title
    if soup.html and soup.html.get('lang'):
        meta['lang'] = soup.html.get('lang').split('-')[0].lower()
    main = pick_main(soup)
    blocks = []
    html_blocks(main, blocks, stats)
    hl = [b[1] for b in blocks if b[0] == 'h']
    minlvl = min(hl) if hl else 1
    return meta, blocks_to_md(blocks, minlvl)


def txt_to_md(text, underscores_are_italic=True):
    text = text.replace('\r\n', '\n').replace('\r', '\n').replace('\ufeff', '')
    m = re.search(r'\*\*\* ?START OF (THE|THIS) PROJECT GUTENBERG[^\n]*\n', text, re.I)
    if m:
        text = text[m.end():]
    m = re.search(r'\*\*\* ?END OF (THE|THIS) PROJECT GUTENBERG', text, re.I)
    if m:
        text = text[:m.start()]
    paras = re.split(r'\n\s*\n', text)
    out = []
    for p in paras:
        lines = [l.rstrip() for l in p.split('\n') if l.strip()]
        if not lines:
            continue
        if len(lines) >= 2 and max(len(l) for l in lines) < 55:
            out.append('\n'.join('| ' + esc_md(l.strip(), underscores=not underscores_are_italic) for l in lines))
        else:
            joined = ''
            for l in lines:
                l = l.strip()
                if joined.endswith('-') and l[:1].islower() and not joined.endswith(' -'):
                    joined = joined[:-1] + l
                else:
                    joined = (joined + ' ' + l).strip()
            out.append(esc_block_start(esc_md(joined, underscores=not underscores_are_italic)))
    return '\n\n'.join(out)


def pdf_to_md(path):
    r = run(['pdftotext', '-enc', 'UTF-8', path, '-'])
    if r.returncode:
        die('pdftotext failed: ' + r.stderr)
    pages = r.stdout.split('\f')
    from collections import Counter
    cnt = Counter(l.strip() for pg in pages for l in pg.split('\n') if 0 < len(l.strip()) < 70)
    rep = {l for l, c in cnt.items() if c >= max(3, len(pages) // 4) and not re.search(r'[.;:,]$', l)}
    keep = []
    for pg in pages:
        ls = [l for l in pg.split('\n')
              if not re.fullmatch(r'\s*[\divxlcIVXLC]{1,6}\s*', l) and l.strip() not in rep]
        keep.append('\n'.join(ls).strip('\n'))
    text = ''
    for pg in keep:
        if not pg:
            continue
        if text and not re.search(r'[.!?:;"”»]\s*$', text):
            text = text.rstrip() + ('' if text.rstrip().endswith('-') else ' ') + pg.lstrip()
            text = re.sub(r'-\s*$', '', text) if False else text
        else:
            text += '\n\n' + pg
    return txt_to_md(text, underscores_are_italic=False)


def fetch(url, dest_dir):
    req = urllib.request.Request(url, headers={'User-Agent': UA, 'Accept-Language': 'en,pl;q=0.8'})
    try:
        with urllib.request.urlopen(req, timeout=60) as r:
            data = r.read()
            ctype = r.headers.get('Content-Type', '').lower()
    except Exception as e:
        die('cannot download %s (%s). The shell may not reach this site: ask the user to '
            'upload the file / saved page, or copy the text with a browser tool '
            '(get_page_text), save it as .txt/.html and run extract on that file. '
            'Do NOT rely on WebFetch: it summarises instead of copying.' % (url, e))
    ext = '.pdf' if ('pdf' in ctype or url.lower().endswith('.pdf')) else \
          '.txt' if ('text/plain' in ctype or url.lower().endswith('.txt')) else \
          '.epub' if ('epub' in ctype or url.lower().endswith('.epub')) else '.html'
    path = os.path.join(dest_dir, 'source' + ext)
    with open(path, 'wb') as f:
        f.write(data)
    return path


def read_text(path):
    raw = open(path, 'rb').read()
    for enc in ('utf-8', 'cp1250', 'latin-1'):
        try:
            return raw.decode(enc)
        except UnicodeDecodeError:
            pass


def cmd_extract(a):
    out = os.path.abspath(a.output)
    os.makedirs(os.path.dirname(out), exist_ok=True)
    src = a.source
    meta = {}
    stats = {'images': 0}
    if re.match(r'https?://', src):
        meta['source'] = src
        path = fetch(src, os.path.dirname(out))
    else:
        path = src
        meta['source'] = os.path.basename(src)
    ext = os.path.splitext(path)[1].lower()
    if ext in ('.html', '.htm', '.xhtml'):
        m, body = html_to_md(read_text(path), stats)
        meta.update({k: v for k, v in m.items() if k not in meta or k == 'title'})
    elif ext in ('.txt', ''):
        body = txt_to_md(read_text(path))
    elif ext in ('.md', '.markdown'):
        body = read_text(path)
        if body.startswith('---'):
            shutil.copy(path, out) if os.path.abspath(path) != out else None
            print('book.md already has a YAML header; copied as is.')
            cmd_outline(argparse.Namespace(book=out))
            return
    elif ext == '.pdf':
        body = pdf_to_md(path)
    elif ext in ('.docx', '.odt', '.epub', '.rtf', '.fb2', '.doc'):
        r = run(['pandoc', path, '-t', 'html5', '--wrap=none'])
        if r.returncode:
            die('pandoc could not read %s: %s' % (path, r.stderr[:400]))
        m, body = html_to_md('<html><body><main>' + r.stdout + '</main></body></html>', stats)
    else:
        die('unknown input type: ' + ext)
    import yaml
    meta.setdefault('title', '')
    head = {'title': meta.get('title', ''), 'author': '', 'translator': '', 'original': '',
            'source': meta.get('source', ''), 'lang': meta.get('lang', 'en'), 'trim': '6x9',
            'toc': True}
    yml = yaml.safe_dump(head, allow_unicode=True, sort_keys=False, width=1000)
    with open(out, 'w', encoding='utf-8') as f:
        f.write('---\n' + yml + '---\n\n' + body.strip() + '\n')
    # baseline copy for later comparison
    shutil.copy(out, out + '.orig')
    print('wrote', out, '(+ .orig baseline)')
    if stats['images']:
        print('NOTE: %d images were skipped' % stats['images'])
    cmd_outline(argparse.Namespace(book=out))


# ============================================================================
#  OUTLINE
# ============================================================================
CAND = re.compile(r'^(\\?\*?\s*)?(chap(ter|\.)|rozdzia|księg|ksieg|część|czesc|book\b|part\b|canto|section|liber|caput|kapitel|chapitre|capitolo|capítulo|preface|introduction|wstęp|przedmowa|epilog|prolog|appendix|dodatek|finis|the end|koniec)', re.I)


def cmd_outline(a):
    lines = open(a.book, encoding='utf-8').read().split('\n')
    start = 0
    if lines and lines[0].strip() == '---':
        start = lines.index('---', 1) + 1
    words = paras = 0
    rows = []
    first = []
    last = []
    in_div = 0
    for i in range(start, len(lines)):
        l = lines[i]
        if not l.strip():
            continue
        if l.startswith(':::'):
            rows.append((i + 1, 'DIV ', l.strip()))
            continue
        if l.startswith('#'):
            rows.append((i + 1, 'H%d  ' % (len(l) - len(l.lstrip('#'))), l.lstrip('#').strip()[:100]))
            continue
        if l.startswith('|'):
            if i == 0 or not lines[i - 1].startswith('|'):
                n = 0
                j = i
                while j < len(lines) and lines[j].startswith('|'):
                    n += 1
                    j += 1
                rows.append((i + 1, 'POEM', '%d lines: %s' % (n, l[1:].strip()[:70])))
            continue
        if l.strip() in ('* * *', '***', '---'):
            rows.append((i + 1, 'HR  ', ''))
            continue
        if i > 0 and lines[i - 1].strip() and not lines[i - 1].startswith(('#', ':::', '|')):
            continue  # continuation line of the same paragraph
        w = len(l.split())
        words += w
        paras += 1
        plain = re.sub(r'[\\*\[\]{}]|\.smallcaps', '', l).strip()
        if w <= 12 and (CAND.match(plain) or re.fullmatch(r'[IVXLC]+\.?', plain)
                        or (plain.isupper() and len(plain) > 3)):
            rows.append((i + 1, 'cand', plain[:100]))
        if len(first) < 3:
            first.append((i + 1, plain[:110]))
        last.append((i + 1, plain[:110]))
        last = last[-3:]
    print('--- %s: %d paragraphs, ~%d words' % (os.path.basename(a.book), paras, words))
    print('--- first paragraphs:')
    for r in first:
        print('  %5d  %s' % r)
    print('--- structure (line, kind, text)   [cand = candidate heading in a paragraph]')
    shown = rows if len(rows) <= 150 else rows[:120] + [(0, '...', '%d more' % (len(rows) - 140))] + rows[-20:]
    for r in shown:
        print('  %5s  %s %s' % r)
    print('--- last paragraphs:')
    for r in last:
        print('  %5d  %s' % r)


# ============================================================================
#  FIX  (structural edits without reading the text)
# ============================================================================
def cmd_fix(a):
    txt = open(a.book, encoding='utf-8').read()
    head, body = '', txt
    if txt.startswith('---'):
        end = txt.find('\n---', 3) + 4
        head, body = txt[:end], txt[end:]
    n = 0
    if a.shift:
        def sh(m):
            lvl = max(1, len(m.group(1)) + a.shift)
            return '#' * lvl + ' '
        body, n = re.subn(r'(?m)^(#{1,6}) ', sh, body)
        print('shifted %d headings by %+d' % (n, a.shift))
    if a.promote:
        rx = re.compile(a.promote)
        lvl = '#' * a.level
        def pr(m):
            line = m.group(1)
            plain = re.sub(r'[\\*]|\[|\]\{\.smallcaps\}', '', line)
            if len(line.split()) <= 15 and rx.search(plain):
                return '\n\n' + lvl + ' ' + line.strip() + '\n\n'
            return m.group(0)
        new = re.sub(r'(?m)(?<=\n\n)([^#|:>\n][^\n]*)(?=\n\n)', pr, '\n\n' + body + '\n\n')
        n = new.count('\n' + lvl + ' ') - ('\n\n' + body).count('\n' + lvl + ' ')
        body = '\n\n' + re.sub(r'\n{3,}', '\n\n', new).strip('\n') + '\n'
        print('promoted %d paragraphs to level %d' % (n, a.level))
    if a.with_title:
        def wt(m):
            nxt = m.group(2).strip()
            if len(nxt.split()) <= 12 and not re.search(r'[.!?:;,]\*?$', nxt.rstrip('*')) or len(nxt.split()) <= 12 and nxt.endswith('.') and len(nxt.split()) <= 8:
                return '%s | %s' % (m.group(1).rstrip(), nxt)
            return m.group(0)
        body, n = re.subn(r'(?m)^(# (?!.*\|).+)\n\n([^#|:>\n][^\n]*)$', wt, body)
        print('attached the following short line as title to %d headings' % n)
    if a.join:
        pat = re.compile(r'(?m)^# (?!.*\|)(.+?)\s*\n\n## (.+?)\s*$')
        segs = re.split(r'(?ms)(^::: \{\.titlepage\}.*?^:::\s*$)', body)
        n = 0
        for k in range(0, len(segs), 2):   # odd segments are title pages: leave them
            def jn(m):
                nonlocal n
                if len(m.group(1).split()) > 5:
                    return m.group(0)
                n += 1
                return '# %s | %s' % (m.group(1).strip(), m.group(2).strip())
            segs[k] = pat.sub(jn, segs[k])
        body = ''.join(segs)
        print('joined %d label+title heading pairs (labels of <= 5 words)' % n)
    if a.unwrap_heading_emphasis:
        def ue(m):
            t = m.group(2)
            parts = [x.strip() for x in t.split(' | ')]
            parts = [re.sub(r'^\[(.*)\]\{\.smallcaps\}$', r'\1', x) for x in parts]
            parts = [re.sub(r'^\*([^*]+)\*$', r'\1', x) for x in parts]
            return m.group(1) + ' | '.join(parts)
        segs = re.split(r'(?ms)(^::: \{\.titlepage\}.*?^:::\s*$)', body)
        n = 0
        for k in range(0, len(segs), 2):
            segs[k], c = re.subn(r'(?m)^(#{1,3} )(.+)$', ue, segs[k])
            n += c
        body = ''.join(segs)
        print('cleaned emphasis in %d headings' % n)
    open(a.book, 'w', encoding='utf-8').write(head + '\n\n' + body.lstrip('\n'))
    cmd_outline(argparse.Namespace(book=a.book))


# ============================================================================
#  BUILD
# ============================================================================
LUA = r'''
local lang = 'en'
local hasparts = false
local nb = 0
local function latex(inl)
  if inl == nil or #inl == 0 then return '' end
  local s = pandoc.write(pandoc.Pandoc({pandoc.Plain(inl)}), 'latex')
  return (s:gsub('%s+$', ''))
end
local function lx(str) return latex({pandoc.Str(str)}) end
local function trim(inl)
  while #inl > 0 and (inl[1].t == 'Space' or inl[1].t == 'SoftBreak') do inl:remove(1) end
  while #inl > 0 and (inl[#inl].t == 'Space' or inl[#inl].t == 'SoftBreak') do inl:remove(#inl) end
  return inl
end
local function splitbar(inl)
  local parts = {pandoc.List()}
  for _, x in ipairs(inl) do
    if x.t == 'Str' and x.text == '|' then parts[#parts+1] = pandoc.List()
    else parts[#parts]:insert(x) end
  end
  for i = 1, #parts do parts[i] = trim(parts[i]) end
  return parts
end
local function bm(level, text)
  nb = nb + 1
  return string.format('\\pdfbookmark[%d]{%s}{bm%d}', level, lx(text), nb)
end

-- pass 0: settings
local P0 = { Meta = function(m)
    if m.lang then lang = pandoc.utils.stringify(m.lang) end
  end,
  Pandoc = function(doc)
    for _, b in ipairs(doc.blocks) do
      if b.t == 'Header' and b.level == 1 and b.classes:includes('part') then hasparts = true end
    end
  end }

-- pass 1: divs
local function tpblock(b)
  if b.t == 'Header' then
    local sz = ({'B','C','D','E','E','E'})[b.level]
    if b.classes:includes('huge') then sz = 'A' end
    return pandoc.RawBlock('latex', string.format('{\\tp%s %s\\par}\\tpgap', sz, latex(b.content)))
  elseif b.t == 'Para' or b.t == 'Plain' then
    return pandoc.RawBlock('latex', '{\\tpP ' .. latex(b.content) .. '\\par}\\tpgap')
  elseif b.t == 'HorizontalRule' then
    return pandoc.RawBlock('latex', '\\vspace{0pt plus 1fill}')
  elseif b.t == 'LineBlock' then
    local ls = {}
    for _, l in ipairs(b.content) do ls[#ls+1] = latex(l) end
    return pandoc.RawBlock('latex', '{\\tpP ' .. table.concat(ls, '\\\\ ') .. '\\par}\\tpgap')
  end
  return b
end
local P1 = { Div = function(d)
  local c = d.classes
  if c:includes('titlepage') then
    local out = {pandoc.RawBlock('latex', '%%TITLEPAGE-BEGIN\n\\begin{titlepagebox}')}
    for _, b in ipairs(d.content) do out[#out+1] = tpblock(b) end
    out[#out+1] = pandoc.RawBlock('latex', '\\end{titlepagebox}\n%%TITLEPAGE-END')
    return out
  end
  for _, k in ipairs({'note','center','right','closing','finis','epigraph'}) do
    if c:includes(k) then
      local out = {pandoc.RawBlock('latex', '\\begin{bk' .. k .. '}')}
      for _, b in ipairs(d.content) do out[#out+1] = b end
      out[#out+1] = pandoc.RawBlock('latex', '\\end{bk' .. k .. '}')
      return out
    end
  end
  if c:includes('pagebreak') then return pandoc.RawBlock('latex', '\\clearpage') end
end }

-- pass 2: headings, verse, rules, quotes, inline niceties
local Q = { en={'“','”','‘','’'}, pl={'„','”','‚','’'}, de={'„','“','‚','‘'},
            fr={'«\u{202F}','\u{202F}»','‹\u{202F}','\u{202F}›'}, cs={'„','“','‚','‘'},
            nl={'“','”','‘','’'}, it={'«','»','“','”'}, es={'«','»','“','”'}, la={'“','”','‘','’'} }
local P2 = {
  Header = function(h)
    local parts = splitbar(h.content)
    local label, title, sub = parts[1] or pandoc.List(), parts[2] or pandoc.List(), parts[3] or pandoc.List()
    local plainlabel = pandoc.utils.stringify(label)
    local plaintitle = pandoc.utils.stringify(title)
    local running = h.attributes['running'] or (plaintitle ~= '' and plaintitle or plainlabel)
    running = running:gsub('[%.,;:]+$', '')
    local both = plainlabel .. ((plainlabel ~= '' and plaintitle ~= '') and ' – ' or '') .. plaintitle
    if h.level == 1 then
      local tocent
      if h.attributes['toc'] then tocent = lx(h.attributes['toc'])
      elseif h.classes:includes('part') then tocent = (#title > 0) and latex(title) or latex(label)
      else
        tocent = (#label > 0 and ('\\textsc{' .. latex(label) .. '}') or '')
        if #title > 0 then tocent = tocent .. (#label > 0 and '\\enspace ' or '') .. latex(title) end
      end
      local cmd = 'chapopen'
      local lvl = hasparts and 1 or 0
      if h.classes:includes('part') then
        cmd = h.classes:includes('alone') and 'partalone' or 'partopen'; lvl = 0
      elseif h.classes:includes('continue') then cmd = 'chapcont' end
      local drop = (cmd ~= 'partalone' and not h.classes:includes('nodrop')) and '%DROP' or ''
      return pandoc.RawBlock('latex', string.format('\\%s{%s}{%s}{%s}{%s}{%s}{%s}%s', cmd,
        latex(label), latex(title), latex(sub), lx(running), tocent, bm(lvl, both), drop))
    elseif h.level == 2 then
      local t = h.attributes['toc'] and lx(h.attributes['toc']) or latex(h.content)
      return pandoc.RawBlock('latex', string.format('\\sechead{%s}{%s}{%s}', latex(h.content), t,
        bm(hasparts and 2 or 1, pandoc.utils.stringify(h.content))))
    else
      return pandoc.RawBlock('latex', '\\subhead{' .. latex(h.content) .. '}')
    end
  end,
  LineBlock = function(lb)
    local ls = {}
    for _, l in ipairs(lb.content) do
      if #l == 0 then ls[#ls+1] = '\\stanzabreak' else ls[#ls+1] = '\\bkline{' .. latex(l) .. '}' end
    end
    return pandoc.RawBlock('latex', '\\begin{bkpoem}\n' .. table.concat(ls, '\n') .. '\n\\end{bkpoem}')
  end,
  HorizontalRule = function() return pandoc.RawBlock('latex', '\\scenebreak') end,
  Quoted = function(q)
    local m = Q[lang] or Q.en
    local o, c = m[1], m[2]
    if q.quotetype == 'SingleQuote' then o, c = m[3], m[4] end
    local r = pandoc.List({pandoc.Str(o)}); r:extend(q.content); r:insert(pandoc.Str(c))
    return r
  end,
  Inlines = function(inl)
    if lang ~= 'pl' and lang ~= 'cs' then return inl end
    for i = 1, #inl - 1 do
      if inl[i].t == 'Str' and inl[i+1].t == 'Space' and
         (inl[i].text:match('^[aiouwzAIOUWZ]$') or inl[i].text:match('^[%(„]?[aiouwzAIOUWZ]$')) then
        inl[i+1] = pandoc.Str('\u{00A0}')
      end
    end
    return inl
  end,
}

-- pass 3: drop caps
local function firststr(inl)
  for i, x in ipairs(inl) do
    if x.t == 'Str' then return inl, i end
    if x.t == 'Emph' or x.t == 'Strong' or x.t == 'SmallCaps' then return firststr(x.content) end
    if x.t ~= 'Space' then return nil end
  end
end
local function nwords(inl)
  local n = 0
  for _, x in ipairs(inl) do if x.t == 'Space' or x.t == 'SoftBreak' then n = n + 1 end end
  return n + 1
end
local P3 = { Pandoc = function(doc)
  local nb = pandoc.List()
  local pending = false
  local usedrop = true
  if doc.meta.dropcaps ~= nil and pandoc.utils.stringify(doc.meta.dropcaps) == 'false' then usedrop = false end
  for _, b in ipairs(doc.blocks) do
    if b.t == 'RawBlock' and b.text:match('%%DROP$') then
      b.text = b.text:gsub('%%DROP$', ''); nb:insert(b); pending = usedrop
    else
      if pending and b.t == 'Para' and nwords(b.content) >= 35 then
        local cont, i = firststr(b.content)
        if cont then
          local s = cont[i].text
          local first = s:match('^[%z\1-\127\194-\244][\128-\191]*')
          local rest = s:sub(#first + 1)
          if first and not first:match('^[%p%d]') and first ~= '' then
            cont:remove(i)
            local lead = string.format('\\noindent\\lettrine{%s}{%s}', lx(first), lx(rest))
            local rawl = pandoc.RawInline('latex', lead)
            if cont == b.content then b.content:insert(1, rawl)
            else b.content:insert(1, rawl) end
          end
        end
      end
      pending = false
      nb:insert(b)
    end
  end
  doc.blocks = nb
  return doc
end }

return {P0, P1, P2, P3}
'''

PREAMBLE = r'''\documentclass[10pt,twoside,openany]{book}
\usepackage[paperwidth=@@PW@@,paperheight=@@PH@@,inner=@@IN@@,outer=@@OUT@@,top=@@TOP@@pt,
  height=@@TH@@pt,headheight=14pt,headsep=@@HS@@,footskip=@@FK@@]{geometry}
\usepackage{fontspec}
\setmainfont{@@FONT@@}[Ligatures={Common,TeX},SmallCapsFeatures={Letters=SmallCaps}]
\newfontfamily\symfont{DejaVu Sans}
\setmonofont{DejaVu Sans Mono}[Scale=0.85]
\newcommand{\ls}[2]{{\addfontfeature{LetterSpace=#1}#2}}
\usepackage{polyglossia}
\setdefaultlanguage{@@LANG@@}
\usepackage[protrusion=true]{microtype}
\usepackage{lettrine,fancyhdr,etoolbox,needspace,varwidth,longtable,booktabs,array,calc,graphicx}
\usepackage{tocloft}
\usepackage[hidelinks,bookmarksopen=true,bookmarksopenlevel=1,pdfpagelabels]{hyperref}
\hypersetup{pdftitle={@@PDFTITLE@@},pdfauthor={@@PDFAUTHOR@@},pdflang={@@LANGCODE@@}}
\providecommand{\tightlist}{\setlength{\itemsep}{0pt}\setlength{\parskip}{0pt}}
\providecommand{\st}[1]{#1}\providecommand{\pandocbounded}[1]{#1}
\makeatletter
\renewcommand\normalsize{\@setfontsize\normalsize{@@FS@@}{@@LEAD@@}%
  \abovedisplayskip 10\p@ \belowdisplayskip \abovedisplayskip}
\renewcommand\small{\@setfontsize\small{@@SMALL@@}{@@SMALLLEAD@@}}
\renewcommand\footnotesize{\@setfontsize\footnotesize{@@FN@@}{@@FNLEAD@@}}
\newcommand{\afterhead}{\@afterindentfalse\@afterheading}
\makeatother
\normalsize
\setlength{\parindent}{1.2em}\setlength{\parskip}{0pt}
\topskip=@@FS@@pt
\clubpenalty=10000 \widowpenalty=10000 \displaywidowpenalty=10000
\tolerance=1200 \emergencystretch=1.5em
\flushbottom\frenchspacing
\setcounter{DefaultLines}{3}
\setlength{\footnotesep}{1.2em}
% ---- page styles
\pagestyle{fancy}\fancyhf{}\renewcommand{\headrulewidth}{0pt}
\fancyhead[LE]{\small\thepage}
\fancyhead[CE]{\small\ls{12}{\textsc{@@RUNTITLE@@}}}
\fancyhead[CO]{\small\itshape\rightmark}
\fancyhead[RO]{\small\thepage}
\fancypagestyle{plain}{\fancyhf{}\renewcommand{\headrulewidth}{0pt}\fancyfoot[C]{\small\thepage}}
\newcommand{\cleartorecto}{\clearpage\ifodd\value{page}\else\thispagestyle{empty}\null\clearpage\fi}
% ---- headings
\newcommand{\headblock}[5]{% label title sub labelsize titlesize
  \begingroup\centering\hyphenpenalty=10000 \exhyphenpenalty=10000
  \ifblank{#1}{}{{\fontsize{#4}{\dimexpr#4pt*5/4\relax}\selectfont\ls{12}{\textsc{#1}}\par}}%
  \ifblank{#2}{}{\ifblank{#1}{}{\vspace{0.7\baselineskip}}{\fontsize{#5}{\dimexpr#5pt*5/4\relax}\selectfont #2\par}}%
  \ifblank{#3}{}{\vspace{0.6\baselineskip}{\small\itshape #3\par}}%
  \vspace{0.8\baselineskip}\rule{0.8in}{0.4pt}\par\endgroup\vspace{1.1\baselineskip}}
\newcommand{\chapopen}[6]{\clearpage\thispagestyle{plain}\phantomsection#6%
  \addcontentsline{toc}{chapter}{#5}\markright{#4}\vspace*{@@CHAPDROP@@}%
  \headblock{#1}{#2}{#3}{12}{13}\afterhead}
\newcommand{\chapcont}[6]{\par\Needspace{10\baselineskip}\vspace{2\baselineskip}\phantomsection#6%
  \addcontentsline{toc}{chapter}{#5}\markright{#4}\headblock{#1}{#2}{#3}{12}{13}\afterhead}
\newcommand{\partopen}[6]{\cleartorecto\thispagestyle{plain}\phantomsection#6%
  \addcontentsline{toc}{part}{#5}\markright{#4}\vspace*{@@CHAPDROP@@}%
  \headblock{#1}{#2}{#3}{11.5}{15}\afterhead}
\newcommand{\partalone}[6]{\cleartorecto\thispagestyle{empty}\phantomsection#6%
  \addcontentsline{toc}{part}{#5}\markright{#4}\vspace*{0.28\textheight}%
  \headblock{#1}{#2}{#3}{12}{17}\clearpage\thispagestyle{empty}\null\clearpage}
\newcommand{\sechead}[3]{\par\Needspace{5\baselineskip}%
  \vspace{1.2\baselineskip plus 0.3\baselineskip minus 0.2\baselineskip}\phantomsection#3%
  \addcontentsline{toc}{section}{#2}%
  {\centering\hyphenpenalty=10000 \fontsize{11.5}{15}\selectfont\ls{12}{#1}\par}%
  \nopagebreak\vspace{0.8\baselineskip}\afterhead}
\newcommand{\subhead}[1]{\par\Needspace{4\baselineskip}%
  \vspace{0.9\baselineskip plus 0.3\baselineskip minus 0.2\baselineskip}%
  {\centering\hyphenpenalty=10000 \small\itshape\advance\leftskip by 0.4in
   \advance\rightskip by 0.4in #1\par}\nopagebreak\vspace{0.5\baselineskip}\afterhead}
\newcommand{\scenebreak}{\par\vspace{0.5\baselineskip}{\centering *\quad*\quad*\par}\vspace{0.5\baselineskip}\afterhead}
% ---- verse and blocks
\newcommand{\bkline}[1]{\par\hangindent=1.5em\hangafter=1 #1\par}
\newcommand{\stanzabreak}{\par\vspace{0.6\baselineskip}}
\newenvironment{bkpoem}{\par\Needspace{4\baselineskip}\vspace{0.6\baselineskip}%
  \begin{center}\begin{varwidth}{0.86\linewidth}\small\raggedright\setlength{\parindent}{0pt}}%
  {\end{varwidth}\end{center}\vspace{0.2\baselineskip}\afterhead}
\renewenvironment{quote}{\par\vspace{0.4\baselineskip}\begin{list}{}{\leftmargin=1.5em\rightmargin=1.5em
  \topsep=0pt\parsep=0pt\listparindent=1.2em}\item\relax\small}{\end{list}\vspace{0.4\baselineskip}}
\newenvironment{bknote}{\par\vspace{0.3\baselineskip}\begingroup\centering\footnotesize\itshape}%
  {\par\endgroup\vspace{0.5\baselineskip}\afterhead}
\newenvironment{bkcenter}{\par\begingroup\centering}{\par\endgroup\afterhead}
\newenvironment{bkright}{\par\begingroup\raggedleft}{\par\endgroup}
\newenvironment{bkclosing}{\par\Needspace{4\baselineskip}\vspace{1.4\baselineskip}\begingroup\centering\itshape}{\par\endgroup\afterhead}
\newenvironment{bkfinis}{\par\vspace{1.2\baselineskip}\begingroup\centering\small\addfontfeature{LetterSpace=20}}{\par\endgroup}
\newenvironment{bkepigraph}{\par\vspace{0.5\baselineskip}\begin{flushright}\begin{varwidth}{0.6\linewidth}\small\itshape\raggedright}%
  {\end{varwidth}\end{flushright}\vspace{0.8\baselineskip}\afterhead}
% ---- title pages
\newcommand{\tpA}{\fontsize{28}{32}\selectfont}
\newcommand{\tpE}{\fontsize{8.5}{11}\selectfont\addfontfeature{LetterSpace=12}}
\newcommand{\tpB}{\fontsize{16}{20}\selectfont}
\newcommand{\tpC}{\fontsize{11.5}{15}\selectfont}
\newcommand{\tpD}{\fontsize{10}{13}\selectfont\addfontfeature{LetterSpace=12}}
\newcommand{\tpP}{\fontsize{9.5}{12.5}\selectfont}
\newcommand{\tpgap}{\par\vspace{0.5em}}
\newenvironment{titlepagebox}{\clearpage\thispagestyle{empty}\vbox to\textheight\bgroup\vspace*{0.25in}%
  \centering\hyphenpenalty=10000 \parindent=0pt }{\par\vspace*{0.25in}\egroup\clearpage}
% ---- contents
\setcounter{tocdepth}{@@TOCDEPTH@@}
\renewcommand{\contentsname}{@@CONTENTS@@}
\renewcommand{\cfttoctitlefont}{\hfill\fontsize{13}{16}\selectfont\addfontfeature{LetterSpace=15}\scshape}
\renewcommand{\cftaftertoctitle}{\hfill}
\setlength{\cftbeforetoctitleskip}{0.3in}\setlength{\cftaftertoctitleskip}{0.8\baselineskip}
\renewcommand{\cftpartfont}{\normalfont\small\itshape}\renewcommand{\cftpartpagefont}{\normalfont\small}
\renewcommand{\cftpartleader}{\cftdotfill{\cftdotsep}}\setlength{\cftbeforepartskip}{0.9em}
\renewcommand{\cftchapfont}{\normalfont\small}\renewcommand{\cftchappagefont}{\normalfont\small}
\renewcommand{\cftchapleader}{\cftdotfill{\cftdotsep}}\setlength{\cftbeforechapskip}{2pt}
\setlength{\cftchapindent}{@@CHAPINDENT@@}\setlength{\cftchapnumwidth}{0pt}
\renewcommand{\cftsecfont}{\normalfont\small}\renewcommand{\cftsecpagefont}{\normalfont\small}
\setlength{\cftsecindent}{@@SECINDENT@@}\setlength{\cftsecnumwidth}{0pt}
\renewcommand{\cftdotsep}{2.5}
\begin{document}
'''

TRIMS = {  # w, h, inner, outer, top, bottom (inches)
    '6x9': (6, 9, .9, .7, .9, .85), '5.5x8.5': (5.5, 8.5, .8, .6, .8, .8),
    '5x8': (5, 8, .75, .55, .75, .78), 'a5': (5.827, 8.268, .79, .59, .79, .8),
}
LANGS = {'en': 'english', 'pl': 'polish', 'de': 'german', 'fr': 'french', 'la': 'latin',
         'it': 'italian', 'es': 'spanish', 'nl': 'dutch', 'cs': 'czech', 'pt': 'portuguese',
         'ru': 'russian', 'sv': 'swedish', 'da': 'danish', 'hu': 'magyar', 'el': 'greek'}
WORDS = {
    'en': dict(contents='Contents', by='by', tr='Translated by', ed='Edited by',
               typeset='This edition is typeset from', kept='The spelling, punctuation and emphasis of the source are preserved; line breaks have been re-flowed.',
               digital='Digital edition', typeface='Typeset in', trim='Trim size'),
    'pl': dict(contents='Spis treści', by='', tr='Przełożył(a)', ed='Opracował(a)',
               typeset='Wydanie złożone na podstawie:', kept='Zachowano pisownię, interpunkcję i wyróżnienia źródła; zmieniono jedynie łamanie wierszy.',
               digital='Wydanie cyfrowe', typeface='Krój pisma:', trim='Format'),
}


def fit_font(name):
    if not shutil.which('fc-list'):
        return name
    fams = run(['fc-list', ':', 'family']).stdout
    have = set(x.strip() for line in fams.split('\n') for x in line.split(','))
    for f in (name, 'TeX Gyre Pagella', 'TeX Gyre Termes', 'Linux Libertine O', 'DejaVu Serif'):
        if f in have:
            if f != name:
                print('NOTE: font "%s" not installed, using "%s"' % (name, f))
            return f
    return name


def font_cmap(fontname):
    try:
        from fontTools.ttLib import TTFont
        path = run(['fc-match', '-f', '%{file}', fontname]).stdout.strip()
        f = TTFont(path, fontNumber=0, lazy=True)
        return set(f.getBestCmap().keys())
    except Exception:
        return None


def tex_esc(s):
    rep = {'\\': r'\textbackslash{}', '{': r'\{', '}': r'\}', '$': r'\$', '&': r'\&',
           '#': r'\#', '^': r'\^{}', '_': r'\_', '%': r'\%', '~': r'\textasciitilde{}'}
    return ''.join(rep.get(c, c) for c in str(s))


def md_inline_tex(texts, lang):
    """convert several short markdown strings to LaTeX in one pandoc call"""
    if not texts:
        return []
    sep = '\n\nZZSEPZZ\n\n'
    r = run(['pandoc', '-f', MD_READER, '-t', 'latex', '--wrap=none', '-M', 'lang=' + lang],
            input=sep.join(t if t else 'ZZEMPTYZZ' for t in texts))
    parts = r.stdout.split('ZZSEPZZ')
    return [p.strip().replace('ZZEMPTYZZ', '') for p in parts]


def split_yaml(path):
    import yaml
    txt = open(path, encoding='utf-8').read()
    meta = {}
    if txt.startswith('---'):
        end = txt.find('\n---', 3)
        meta = yaml.safe_load(txt[3:end]) or {}
    return meta


def cmd_build(a):
    book = os.path.abspath(a.book)
    meta = split_yaml(book)
    for k in list(meta):
        if meta[k] is None:
            meta[k] = ''
    if not meta.get('title'):
        die('YAML "title" is empty')
    lang = str(meta.get('lang') or 'en').lower()
    W = WORDS.get(lang, WORDS['en'])
    trim = str(meta.get('trim') or '6x9').lower().replace(' ', '')
    if trim not in TRIMS:
        die('trim must be one of ' + ', '.join(TRIMS))
    pw, ph, inner, outer, top, bottom = TRIMS[trim]
    fs = float(meta.get('fontsize') or 10.5)
    lead = round(fs * 4 / 3 * 2) / 2
    avail = (ph - top - bottom) * 72.27
    nlines = int((avail - fs) // lead) + 1
    th = fs + (nlines - 1) * lead
    font = fit_font(str(meta.get('font') or 'TeX Gyre Pagella'))
    work = os.path.splitext(book)[0] + '_build'
    os.makedirs(work, exist_ok=True)
    luaf = os.path.join(work, 'bookify.lua')
    open(luaf, 'w', encoding='utf-8').write(LUA)
    r = run(['pandoc', book, '-f', MD_READER, '-t', 'latex', '--wrap=preserve',
             '--lua-filter', luaf, '-M', 'lang=' + lang])
    if r.returncode:
        die('pandoc: ' + r.stderr[:1500])
    body = r.stdout
    if r.stderr.strip():
        print('pandoc:', r.stderr.strip()[:600])
    # first facsimile title page -> front matter
    custom_tp = ''
    m = re.search(r'%%TITLEPAGE-BEGIN\n(.*?)\n%%TITLEPAGE-END', body, re.S)
    if m:
        custom_tp = m.group(1)
        body = body[:m.start()] + body[m.end():]
    body = body.replace('%%TITLEPAGE-BEGIN\n', '').replace('\n%%TITLEPAGE-END', '')
    # glyphs missing from the main font -> fallback font
    cmap = font_cmap(font)
    if cmap:
        missing = sorted({c for c in body if ord(c) > 0x2000 and ord(c) not in cmap
                          and c not in '\u00a0\u202f'})
        if missing:
            print('NOTE: glyphs not in %s set in DejaVu Sans: %s' % (font, ''.join(missing)))
            body = re.sub('[' + re.escape(''.join(missing)) + ']', lambda x: r'{\symfont ' + x.group(0) + '}', body)
    # metadata to LaTeX
    keys = ['title', 'subtitle', 'author', 'translator', 'editor', 'original', 'license', 'colophon', 'edition']
    conv = dict(zip(keys, md_inline_tex([str(meta.get(k) or '') for k in keys], lang)))
    title, author = conv['title'], conv['author']
    runtitle = tex_esc(meta.get('running-title') or meta.get('title'))
    year = datetime.date.today().year
    def strip_tex(s):
        return re.sub(r'\\[a-zA-Z]+\{?|[{}]', '', s)
    pre = PREAMBLE
    subs = {
        'PW': '%sin' % pw, 'PH': '%sin' % ph, 'IN': '%sin' % inner, 'OUT': '%sin' % outer,
        'TOP': '%.2f' % (top * 72.27), 'TH': '%.2f' % th, 'HS': '0.2in', 'FK': '0.4in',
        'FONT': font, 'LANG': LANGS.get(lang, 'english'), 'LANGCODE': lang,
        'PDFTITLE': tex_esc(meta.get('title')), 'PDFAUTHOR': tex_esc(meta.get('author') or ''),
        'FS': '%g' % fs, 'LEAD': '%g' % lead, 'SMALL': '%g' % (fs - 1), 'SMALLLEAD': '%g' % (lead - 2),
        'FN': '%g' % (fs - 2), 'FNLEAD': '%g' % (lead - 3), 'RUNTITLE': runtitle,
        'CHAPDROP': '%.2fin' % (0.85 * ph / 9), 'TOCDEPTH': '1' if str(meta.get('toc-depth', 1)) == '2' else '0',
        'CONTENTS': W['contents'],
        'CHAPINDENT': '1.4em' if '\\partopen' in body or '\\partalone' in body else '0pt',
        'SECINDENT': '2.8em' if '\\partopen' in body or '\\partalone' in body else '1.4em',
    }
    for k, v in subs.items():
        pre = pre.replace('@@%s@@' % k, v)
    fm = [r'\pagenumbering{roman}']
    if meta.get('half-title', True) is not False:
        fm.append(r'\thispagestyle{empty}\vspace*{0.3\textheight}{\centering\hyphenpenalty=10000 '
                  r'{\fontsize{15}{20}\selectfont\ls{8}{\textsc{%s}}\par}}\clearpage'
                  r'\thispagestyle{empty}\null\clearpage' % title)
    if custom_tp:
        fm.append(r'\phantomsection\pdfbookmark[0]{Title page}{titlepage}' + custom_tp)
    else:
        tp = [r'\clearpage\thispagestyle{empty}\phantomsection\pdfbookmark[0]{Title page}{titlepage}',
              r'\vspace*{0.12\textheight}\begin{center}\hyphenpenalty=10000 ']
        if author:
            tp.append(r'{\fontsize{12}{15}\selectfont\ls{15}{\textsc{%s}}\par}\vspace{2.2em}' % author)
        tp.append(r'{\fontsize{22}{27}\selectfont %s\par}' % title)
        if conv['subtitle']:
            tp.append(r'\vspace{1em}{\fontsize{12}{15}\selectfont\itshape %s\par}' % conv['subtitle'])
        tp.append(r'\vspace{0.8em}\rule{0.8in}{0.4pt}\par')
        if conv['translator']:
            tp.append(r'\vspace{1.2em}{\small %s %s\par}' % (W['tr'], conv['translator']))
        if conv['editor']:
            tp.append(r'\vspace{0.4em}{\small %s %s\par}' % (W['ed'], conv['editor']))
        tp.append(r'\vfill')
        if conv['original']:
            tp.append(r'{\small\itshape %s\par}' % conv['original'])
        tp.append(r'\end{center}\clearpage')
        fm.append('\n'.join(tp))
    # colophon (verso of title page)
    col = [r'\thispagestyle{empty}\vspace*{\fill}\begingroup\small\setlength{\parindent}{0pt}\setlength{\parskip}{0.6em}',
           r'\begin{center}{\normalsize\textsc{%s}}%s\end{center}' % (title,
               (r'\\[0.2em]' + (W['by'] + ' ' if W['by'] else '') + author) if author else '')]
    line = []
    if conv['translator']:
        line.append('%s %s.' % (W['tr'], conv['translator'].rstrip('.')))
    if conv['original']:
        line.append(conv['original'].rstrip('.') + '.')
    if line:
        col.append(' '.join(line) + '\n')
    src = meta.get('source') or ''
    if src:
        shown = re.sub(r'^https?://(www\.)?', '', str(src)).rstrip('/')
        col.append(r'%s {\raggedright\ttfamily\footnotesize %s\par} %s' % (W['typeset'], tex_esc(shown), W['kept']) + '\n')
    if conv['colophon']:
        col.append(conv['colophon'] + '\n')
    if conv['license']:
        col.append(conv['license'] + '\n')
    col.append(r'\medskip ' + (conv['edition'] or '%s, %d' % (W['digital'], year)) +
               '. %s %s. %s %s.' % (W['typeface'], font.replace('TeX Gyre ', 'TeX Gyre '), W['trim'],
                                     ('A5' if trim == 'a5' else trim.replace('x', r'\,\texttimes\,') + ' in')))
    col.append(r'\endgroup\vspace*{0.4in}\clearpage')
    fm.append('\n'.join(col))
    if meta.get('toc', True) is not False and ('\\chapopen' in body or '\\partopen' in body or '\\chapcont' in body or '\\partalone' in body):
        fm.append(r'\phantomsection\pdfbookmark[0]{%s}{contents}\thispagestyle{plain}\tableofcontents\thispagestyle{plain}' % W['contents'])
    fm.append(r'\cleartorecto\pagenumbering{arabic}')
    doc = pre + '\n'.join(fm) + '\n' + body + '\n\\end{document}\n'
    texf = os.path.join(work, 'book.tex')
    open(texf, 'w', encoding='utf-8').write(doc)
    json.dump({'top': top * 72, 'height': th * 72 / 72.27, 'width': pw * 72},
              open(os.path.join(work, 'geometry.json'), 'w'))
    passes = 3 if meta.get('toc', True) is not False else 2
    for i in range(passes):
        r = run(['xelatex', '-interaction=nonstopmode', '-halt-on-error', 'book.tex'], cwd=work)
        if r.returncode:
            log = open(os.path.join(work, 'book.log'), encoding='utf-8', errors='replace').read()
            err = re.findall(r'^!.*?(?=\n\n|\Z)', log, re.S | re.M)
            die('xelatex failed (pass %d):\n%s\n(see %s)' % (i + 1, '\n'.join(err)[:1500], texf))
    log = open(os.path.join(work, 'book.log'), encoding='utf-8', errors='replace').read()
    over = [float(x) for x in re.findall(r'Overfull \\hbox \(([\d.]+)pt too wide\)', log)]
    name = meta.get('output') or slug('%s %s' % (meta.get('author') or '', meta.get('title')))[:80] + '.pdf'
    out = os.path.abspath(a.output) if a.output else os.path.join(os.path.dirname(book), name)
    shutil.copy(os.path.join(work, 'book.pdf'), out)
    npages = len(__import__('pypdf').PdfReader(out).pages)
    print('PDF: %s  (%d pages, %s, %s %gpt, %d lines/page)' % (out, npages, trim, font, fs, nlines))
    bad = [x for x in over if x > 1.0]
    if bad:
        print('WARNING: %d lines stick out into the margin (max %.1fpt) - see overfull in %s'
              % (len(bad), max(bad), os.path.join(work, 'book.log')))
    if not a.no_verify:
        ok = cmd_verify(argparse.Namespace(book=book, pdf=out, quiet=True))
    if not a.no_preview:
        cmd_preview(argparse.Namespace(pdf=out, pages=None, dpi=None))


def slug(s):
    s = unicodedata.normalize('NFKD', s).encode('ascii', 'ignore').decode()
    return re.sub(r'[^A-Za-z0-9]+', '_', s).strip('_') or 'book'


# ============================================================================
#  VERIFY
# ============================================================================
def norm_tokens(s, strip_digits=False):
    s = unicodedata.normalize('NFKD', s)
    out = []
    for w in s.split():
        w = ''.join(c for c in w.lower() if c.isalnum())
        if strip_digits:
            w = re.sub(r'(?<=[^\d])\d+$', '', w)
        if w:
            out.append(w)
    return out


VERIFY_LUA = r'''
local seen = false
local notes = pandoc.List()
return {{ Div = function(d)
    if d.classes:includes('titlepage') and not seen then seen = true; return {} end
  end,
  Note = function(n) notes:insert(pandoc.utils.stringify(n.content)); return {} end,
  Pandoc = function(doc)
    doc.blocks:insert(pandoc.RawBlock('plain', 'ZZNOTESZZ\n' .. table.concat(notes, '\nZZNOTEZZ\n')))
    return doc end }}
'''


def cmd_verify(a):
    from pypdf import PdfReader
    work = os.path.splitext(os.path.abspath(a.book))[0] + '_build'
    gfile = os.path.join(work, 'geometry.json')
    geo = json.load(open(gfile)) if os.path.exists(gfile) else None
    lf = os.path.join(work, 'verify.lua') if os.path.isdir(work) else tempfile.mktemp(suffix='.lua')
    open(lf, 'w').write(VERIFY_LUA)
    r = run(['pandoc', a.book, '-f', MD_READER, '-t', 'plain', '--wrap=none', '--lua-filter', lf])
    if r.returncode:
        die('pandoc: ' + r.stderr[:800])
    main, _, notes = r.stdout.partition('ZZNOTESZZ')
    notes = [n for n in notes.split('ZZNOTEZZ') if n.strip()]
    reader = PdfReader(a.pdf)
    labels = reader.page_labels
    start = labels.index('1') if '1' in labels else 0
    texts = []
    for p in range(start + 1, len(reader.pages) + 1):
        cmd = ['pdftotext', '-raw', '-f', str(p), '-l', str(p)]
        if geo:
            cmd += ['-x', '0', '-y', str(int(geo['top']) - 2), '-W', str(int(geo['width'])),
                    '-H', str(int(geo['height']) + 4)]
        texts.append(run(cmd + [a.pdf, '-']).stdout)
    pdf = re.sub(r'-\n', '', '\n'.join(texts).replace('\f', ''))
    sd = bool(notes)
    A = norm_tokens(main, sd)
    B = norm_tokens(pdf, sd)
    for n in notes:   # footnotes sit at page bottoms: remove them from the PDF stream
        nt = norm_tokens(n, sd)
        for i in range(len(B) - len(nt) + 1):
            if B[i:i + len(nt)] == nt:
                del B[i:i + len(nt)]
                break
    sm = difflib.SequenceMatcher(None, A, B, autojunk=False)
    real = []
    for tag, i1, i2, j1, j2 in sm.get_opcodes():
        if tag == 'equal' or ''.join(A[i1:i2]) == ''.join(B[j1:j2]):
            continue
        real.append((tag, i1, i2, j1, j2))
    missing = sum(i2 - i1 for _, i1, i2, _, _ in real)
    print('VERIFY: %d words in book.md, %d in PDF body; %d differing spots, %d source words not matched'
          % (len(A), len(B), len(real), missing))
    for tag, i1, i2, j1, j2 in real[:15]:
        print('  %-7s md: %s\n          pdf: %s' % (tag, ' '.join(A[max(0, i1 - 4):i2 + 4])[:120],
                                                  ' '.join(B[max(0, j1 - 4):j2 + 4])[:120]))
    if not real:
        print('VERIFY OK: the PDF contains every word of book.md, in order.')
    return not real


# ============================================================================
#  PREVIEW
# ============================================================================
def cmd_preview(a):
    from PIL import Image
    out_dir = os.path.splitext(os.path.abspath(a.pdf))[0] + '_preview'
    shutil.rmtree(out_dir, ignore_errors=True)
    os.makedirs(out_dir)
    if a.pages:
        pages = []
        for part in a.pages.split(','):
            if '-' in part:
                x, y = part.split('-')
                pages += list(range(int(x), int(y) + 1))
            else:
                pages.append(int(part))
        dpi = a.dpi or 90
        ims = []
        for p in pages:
            run(['pdftoppm', '-r', str(dpi), '-png', '-f', str(p), '-l', str(p), '-singlefile', a.pdf,
                 os.path.join(out_dir, 'p%03d' % p)])
            ims.append(Image.open(os.path.join(out_dir, 'p%03d.png' % p)))
        outs = []
        for k in range(0, len(ims), 3):
            grp = ims[k:k + 3]
            w, h = grp[0].size
            S = Image.new('RGB', (len(grp) * (w + 8) + 8, h + 16), (110, 110, 110))
            for i, im in enumerate(grp):
                S.paste(im, (8 + i * (w + 8), 8))
            f = os.path.join(out_dir, 'pages_%s.png' % '_'.join(str(p) for p in pages[k:k + 3]))
            S.save(f)
            outs.append(f)
        print('PREVIEW:', *outs)
        return
    dpi = a.dpi or 36
    run(['pdftoppm', '-r', str(dpi), '-png', a.pdf, os.path.join(out_dir, 'p')])
    files = sorted(glob.glob(os.path.join(out_dir, 'p-*.png')))
    w, h = Image.open(files[0]).size
    cols, per = 10, 40
    outs = []
    for s in range(0, len(files), per):
        fs = files[s:s + per]
        rows = (len(fs) + cols - 1) // cols
        S = Image.new('RGB', (cols * (w + 4) + 4, rows * (h + 4) + 4), (110, 110, 110))
        for k, f in enumerate(fs):
            S.paste(Image.open(f), (4 + (k % cols) * (w + 4), 4 + (k // cols) * (h + 4)))
        f = os.path.join(out_dir, 'sheet_%02d.png' % (s // per + 1))
        S.save(f)
        outs.append(f)
    for f in files:
        os.remove(f)
    print('PREVIEW: %d contact sheet(s), 40 pages each (file page numbers, row-major):' % len(outs))
    for f in outs:
        print('  ' + f)


# ============================================================================
def main():
    import signal
    signal.signal(signal.SIGPIPE, signal.SIG_DFL)
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sp = p.add_subparsers(dest='cmd', required=True)
    e = sp.add_parser('extract'); e.add_argument('source'); e.add_argument('-o', '--output', default='book/book.md')
    o = sp.add_parser('outline'); o.add_argument('book')
    b = sp.add_parser('build'); b.add_argument('book'); b.add_argument('-o', '--output')
    b.add_argument('--no-verify', action='store_true'); b.add_argument('--no-preview', action='store_true')
    f = sp.add_parser('fix', help='structural edits'); f.add_argument('book')
    f.add_argument('--shift', type=int, default=0, help='add N to every heading level')
    f.add_argument('--promote', help='regex: short paragraphs matching it become headings')
    f.add_argument('--level', type=int, default=1, help='level for --promote')
    f.add_argument('--with-title', action='store_true', help='"# Chapter 1" + short paragraph -> "# Chapter 1 | Title"')
    f.add_argument('--join', action='store_true', help='"# Chap. II." + "## Title" -> "# Chap. II. | Title"')
    f.add_argument('--unwrap-heading-emphasis', action='store_true', help='drop whole-heading *italic*/smallcaps')
    v = sp.add_parser('verify'); v.add_argument('book'); v.add_argument('pdf')
    pr = sp.add_parser('preview'); pr.add_argument('pdf'); pr.add_argument('--pages'); pr.add_argument('--dpi', type=int)
    sp.add_parser('spec')
    sp.add_parser('check')
    a = p.parse_args()
    if a.cmd == 'spec':
        print(SPEC)
    elif a.cmd == 'check':
        for t in ('pandoc', 'xelatex', 'pdftotext', 'pdftoppm', 'fc-list'):
            print('%-10s %s' % (t, shutil.which(t) or 'MISSING'))
        for m in ('bs4', 'yaml', 'pypdf', 'PIL'):
            try:
                __import__(m); print('%-10s ok' % m)
            except ImportError:
                print('%-10s MISSING  (pip install --break-system-packages %s)' % (m, {'bs4': 'beautifulsoup4', 'yaml': 'pyyaml', 'PIL': 'pillow'}.get(m, m)))
        print('font      ', fit_font('TeX Gyre Pagella'))
    else:
        globals()['cmd_' + a.cmd](a)


if __name__ == '__main__':
    main()
