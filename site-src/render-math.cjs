const fs = require('fs');
const katex = require('katex');
const items = JSON.parse(fs.readFileSync(0, 'utf8'));
const rendered = items.map(({tex, display}) => katex.renderToString(tex, {
  displayMode: display,
  throwOnError: true,
  strict: 'error',
  trust: false,
  output: 'htmlAndMathml',
  macros: {'\\Tr': '\\operatorname{Tr}', '\\dd': '\\mathrm{d}', '\\id': '\\mathbf{1}'}
}));
process.stdout.write(JSON.stringify(rendered));
