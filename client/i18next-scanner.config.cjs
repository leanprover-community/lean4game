const typescriptTransform = require('i18next-scanner-typescript');

const fs = require('fs');
const chalk = require('chalk');

module.exports = {
    input: [
        'client/src/**/*.{tsx,ts}',
        // Use ! to filter out files or directories
        '!client/i18n/**',
        '!**/node_modules/**',
    ],
    output: './client/public/locales',
    options: {
        debug: true,
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
        lngs: ['en','de'],
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
            loadPath: './{{lng}}/{{ns}}.json',
            savePath: './{{lng}}/{{ns}}.json',
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

            // const content = fs.readFileSync(file.path, enc);
            // let count = 0;

            // parser.parseFuncFromString(content, { list: ['i18n._', 'i18n.__'] }, (key, options) => {
            //     parser.set(key, Object.assign({}, options, {
            //         nsSeparator: false,
            //         keySeparator: false
            //     }));
            //     ++count;
            // });

            // if (count > 0) {
            //     console.log(`[i18next-scanner] transform: count=${chalk.cyan(count)}, file=${chalk.yellow(JSON.stringify(file.relative))}`);
            // }

            done();
        }
      ),

};
