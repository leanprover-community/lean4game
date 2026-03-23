# Guide for translators

This page is about translating a single game.  For translating the game interface, see [this page](translation-interface.md) instead.  For the game maintainer's point of view, see [this page](translation-guide-for-game-maintainers.md).

Note that you can base your translation on any existing language ([see details below]((Optional:)-choose-a-different-source-language)).

## 1. Files needed

All you need to start working on a translation of a game's `.pot` file, which you will usually find at `.i18n/en/Game.pot` within the game repository. Some games also include a short list of glossary terms, which you will usually find at `.i18n/en/glossary.csv`.  

Some game repositories will moreover include specific instructions for translators.  For example, see [this guidelines](https://github.com/hhu-adam/Robo/blob/main/docs/TranslationGuide.md) for more specific information on how to translate the game Scribble.  Make sure to read those specific guidelines in addition to the generic instructions in this file.

## 2. (Optional:) Translate glossary terms

If your game includes a glossary list, translate these terms first.  Save the file in `csv` format, with the original entries left and the translations to the right of the comma.

## 3. Translate the .po-file

We recommend using  [Poedit](https://poedit.net/) to work on the translations.  In Poedit, go to `File` `>` `New From POT/PO File …` and open the file `.i18n/template/Game.pot`. Select the language you want to translate into and save the file as a `po` file.  Within the Game repository, the final file will eventually need to be located at `.i18n/{language}/Game.po`, where {language} is the ISO language code.

You can now enter your translations line by line in Poedit.  Be careful to preserve the [formatting](#string-format).

There are various tools that can significantly simplify the translation process, but these typically require a paid subscription (for Poedit and/or an AI tool).  Please contact the maintainers of the game if you're willing to help, but do not have access to such tools.  

### (Optional:) Choose a different source language

With a paid subscription for Poedit, you can select any existing language as a source language for your translation.  Select `Translation` `>` `Source Text` `>` `Load From Another File` and select one of the existing files `.i18n/{source language}/Game.po`.

Alternatively, tools like `pomerge` might be useful: it allows you to do something like
```
pomerge de-en.po en-fr.po -o de-fr.po
```
to merge a translation for `de` to `en` and a translation from `en` to `fr` into a translation from `de` to `fr`.

### (Optional:) Pretranslate with AI
We highly recommend first pretranslating with machine translation tools.  
The workflow is:

1. If you have a glossary file from the previous step, load it into Poedit as follows:   

  Click `View` `>` `Show Terminology Tab`.  In the tab, click the litte `+` symbol next to search box, and then `Import Glossary From CSV File…`.  Select the `csv` file that you created above.

2. Pretranslate using machine translation tools (`Translation` `>` `Pretranslate`).  Make sure to tick `Use glossary` if you have imported a glossary in the previous step.  In our limited experience, pretranslation with GPT works significantly better than with DeepL.  See [here](https://github.com/hhu-adam/Robo/blob/main/docs/TranslationGuide.md#2-pretranslate-using-machine-translation) for an example of a prompt.

3. Review and revise the pretranslateds strings.  Again, pay attention to [formatting](#string-format).

### String format

In the strings in `Game.pot`, codeblocks (starting with one or many backticks (\`)) and latex blocks (starting with one or two `$`) have been replaced by placeholders `§n`.  You can see the contents of these placeholders in the comments.  You can, but you do not have to use these placeholders in your translation.  Placeholders help to (a) aviod typos created by manually copying over codeblocks or latex blocks, and (b) to improve interaction with automated translation tooling (see above).

## 4. Ask someone to review your translation

Ideally, please ask someone from the lean community to review your translation, or ask the game's maintainer to find someone for you.

