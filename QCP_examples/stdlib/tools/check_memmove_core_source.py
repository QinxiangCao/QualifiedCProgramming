#!/usr/bin/env python3
"""Check glibc byte extraction, entry adaptation, and callee contracts."""
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[3]


def strip_comments(text):
    return re.sub(r'/\*.*?\*/', '', text, flags=re.S)


def body(text, name):
    text = strip_comments(text)
    pos = text.index('{', text.index(name + '('))
    depth = 1
    end = pos + 1
    while depth:
        depth += (text[end] == '{') - (text[end] == '}')
        end += 1
    return text[pos+1:end-1]


def tokens(text):
    return re.findall(r'[A-Za-z_]\w*|\d+|\+=|-=|==|[^\s]', text)


def main():
    upstream = (ROOT / 'docs/stdlib/upstream/glibc/glibc-2.40/sysdeps/generic/memcopy.h').read_text()
    candidate = (ROOT / 'QCP_examples/stdlib/glibc/memmove_loops.c').read_text()
    for direction, function in [('FWD', 'mm_copy_forward'), ('BWD', 'mm_copy_backward')]:
        match = re.search(r'#define BYTE_COPY_' + direction + r'\([^\n]+\n(.*?while \(0\))', upstream, re.S)
        macro = match.group(1).replace('\\', '')
        macro = macro[macro.index('{')+1:macro.rindex('}')]
        for old, new in [('__nbytes', 'remaining'), ('__x', 'x'), ('src_bp', 'src'),
                         ('src_ep', 'src'), ('dst_bp', 'dest'), ('dst_ep', 'dest'),
                         ('(nbytes)', 'n')]:
            macro = macro.replace(old, new)
        macro = macro.replace('((byte *) src)[0]', 'mm_load_byte(src)')
        macro = macro.replace('((byte *) dest)[0] = x;', 'mm_store_byte(dest,x);')
        macro = re.sub(r'\bbyte\b', 'unsigned char', macro)
        if direction == 'BWD':
            # Move the uninitialised scalar declaration to its first assignment.
            macro = macro.replace('unsigned char x;', '').replace('x = mm_load_byte(src);', 'unsigned char x = mm_load_byte(src);')
            # Endpoint setup comes from memmove.c immediately before BYTE_COPY_BWD.
            macro = 'src += n; dest += n;' + macro
        assert tokens(macro) == tokens(body(candidate, function)), function
        print(function + ': executable tokens match the documented macro extraction')
    helpers = (ROOT / 'QCP_examples/stdlib/glibc/memmove_bytes.c').read_text()
    assert tokens(body(helpers, 'mm_load_byte')) == tokens('return *p;')
    assert tokens(body(helpers, 'mm_store_byte')) == tokens('*p = value;')
    declarations = (ROOT / 'QCP_examples/stdlib/glibc/memmove_bytes.h').read_text()
    for name in ('mm_load_byte', 'mm_store_byte'):
        pattern = r'(?:unsigned char|void) ' + name + r'\([^;{]*?/\*@.*?\*/'
        implementation_contract = re.search(pattern, helpers, re.S).group()
        caller_contract = re.search(pattern, declarations, re.S).group()
        assert implementation_contract == caller_contract, name + ' contract mismatch'
    print('byte access helpers: exact scalar load/store')
    loop_header = (ROOT / 'QCP_examples/stdlib/glibc/memmove_loops.h').read_text()
    pattern = r'void mm_copy_(?:forward|backward)\([^;{]*?/\*@.*?\*/'
    assert re.findall(pattern, candidate, re.S) == re.findall(pattern, loop_header, re.S)
    print('loop declarations: all caller contracts match proved definitions')

    entry = (ROOT / 'QCP_examples/stdlib/glibc/memmove.c').read_text()
    public_header = (ROOT / 'QCP_examples/stdlib/glibc/memmove_spec.h').read_text()
    public_pattern = r'void \*memmove\([^;{]*?/\*@.*?\*/'
    public_contracts = re.findall(public_pattern, public_header, re.S)
    entry_contracts = re.findall(public_pattern, entry, re.S)
    assert public_contracts == [c.replace(' <= byte_memory_spec', '')
                                for c in entry_contracts[:5]]
    assert len(public_contracts) == 5 and len(entry_contracts) == 6
    print('public header: five contracts match the proved entry refinements')
    original = (ROOT / 'docs/stdlib/upstream/glibc/glibc-2.40/string/memmove.c').read_text()
    assert 'if (dstp - srcp >= len)' in strip_comments(original)
    # Explicitly check the selected byte-only adaptation, not the omitted
    # memcpy/page/word paths. The backward helper includes endpoint setup.
    expected = '''
      if (n == 0) return dest;
      unsigned long long dstp = (unsigned long long)dest;
      unsigned long long srcp = (unsigned long long)src;
      if (dstp - srcp >= n) {
        mm_copy_forward((unsigned char *)dest,(const unsigned char *)src,n);
      } else {
        mm_copy_backward((unsigned char *)dest,(const unsigned char *)src,n);
      }
      return dest;
    '''
    assert tokens(body(entry, 'memmove')) == tokens(expected)
    print('entry: unsigned glibc direction test and documented byte-only adaptation')


if __name__ == '__main__':
    main()
