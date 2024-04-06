const lean4gameConfig = require("./src/config.json")

const typescriptTransform = require('i18next-scanner-typescript');

const fs = require('fs');
const chalk = require('chalk');
const eol = require('eol');
const path = require('path');
const VirtualFile = require('vinyl');

function flush(done) {
  const { parser } = this;
  const { options } = parser;

  // Flush to resource store
  const resStore = parser.get({ sort: options.sort });
  const { jsonIndent } = options.resource;
  const lineEnding = String(options.resource.lineEnding).toLowerCase();

  Object.keys(resStore).forEach((lng) => {
    const namespaces = resStore[lng];

    Object.keys(namespaces).forEach((ns) => {
      const resPath = parser.formatResourceSavePath(lng, ns);
      let resContent;
      try {
        resContent = JSON.parse(
          fs.readFileSync(
            fs.realpathSync(path.join('public', 'locales', resPath))
          ).toString('utf-8')
        );
      } catch (e) {
        console.log("no previous translation found!")
        resContent = {};
      }
      const obj = { ...namespaces[ns], ...resContent };
      let text = JSON.stringify(obj, null, jsonIndent) + '\n';

      if (lineEnding === 'auto') {
        text = eol.auto(text);
      } else if (lineEnding === '\r\n' || lineEnding === 'crlf') {
        text = eol.crlf(text);
      } else if (lineEnding === '\n' || lineEnding === 'lf') {
        text = eol.lf(text);
      } else if (lineEnding === '\r' || lineEnding === 'cr') {
        text = eol.cr(text);
      } else { // Defaults to LF
        text = eol.lf(text);
      }

      let contents = null;

      try {
        // "Buffer.from(string[, encoding])" is added in Node.js v5.10.0
        contents = Buffer.from(text);
      } catch (e) {
        // Fallback to "new Buffer(string[, encoding])" which is deprecated since Node.js v6.0.0
        contents = new Buffer(text);
      }

      this.push(new VirtualFile({
        path: resPath,
        contents: contents
      }));
    });
  });

  done();
}


module.exports = {
  input: [
    'client/src/**/*.{tsx,ts}',
    // Use ! to filter out files or directories
    '!client/i18n/**',
    '!**/node_modules/**',
  ],
  options: {
    debug: true,
    removeUnusedKeys: true,
    func: {
      list: ['i18next.t', 'i18n.t', 't'],
      extensions: ['.js', '.jsx'] // not .ts or .tsx since we use i18next-scanner-typescript!
    },
    trans: {
      component: 'Trans',
      i18nKey: 'i18nKey',
      defaultsKey: 'defaults',
      extensions: ['.js', '.jsx'], // not .ts or .tsx since we use i18next-scanner-typescript!
      fallbackKey: (ns, value) => {return value},

      // https://react.i18next.com/latest/trans-component#usage-with-simple-html-elements-like-less-than-br-greater-than-and-others-v10.4.0
      supportBasicHtmlNodes: true, // Enables keeping the name of simple nodes (e.g. <br/>) in translations instead of indexed keys.
      keepBasicHtmlNodesFor: ['br', 'strong', 'i', 'p'], // Which nodes are allowed to be kept in translations during defaultValue generation of <Trans>.

      // // https://github.com/acornjs/acorn/tree/master/acorn#interface
      // acorn: {
      //     ecmaVersion: 2020,
      //     sourceType: 'module', // defaults to 'module'
      // }
    },
    lngs: lean4gameConfig.languages.map(e => e.iso),
    ns: [],
    defaultLng: 'en',
    defaultNs: 'translation',
    defaultValue: (lng, ns, key) => {
      if (lng === 'en') {
        return key; // Use key as value for base language
      }
      return ''; // Return empty string for other languages
    },
    resource: {
      loadPath: './client/public/locales/{{lng}}/{{ns}}.json',
      savePath: './client/public/locales/{{lng}}/{{ns}}.json',
      jsonIndent: 2,
      lineEnding: '\n'
    },
    nsSeparator: false, // namespace separator
    keySeparator: false, // key separator
    plurals: false,
    interpolation: {
      prefix: '{{',
      suffix: '}}'
    },
    metadata: {},
    allowDynamicKeys: false,
  },

  transform: typescriptTransform(
    // options
    {
      // default value for extensions
      extensions: [".ts", ".tsx"],
      // optional ts configuration
      tsOptions: {
        target: "es2017",
      },
    },

    function(outputText, file, enc, done) {
      'use strict';
      const parser = this.parser;

      parser.parseTransFromString(outputText);
      parser.parseFuncFromString(outputText);

      done();
    }
  ),

};
