#!/usr/bin/env bash

cd "$(dirname "$0")"

original_font="../src/assets/fonts/NotoColorEmoji-Regular.ttf"
subset_font="../src/assets/fonts/NotoColorEmoji-Subset.woff2"

# set of glyphs which should be displayed as emojis
subset="🎉❌✅💥🎭⏳🟡💡🐙🔍🏁"

pyftsubset "$original_font" \
  --output-file="$subset_font" \
  --text="$subset" \
  --layout-features='*' \
  --flavor=woff2

# Cross-platform file size function
filesize() {
  stat -f%z "$1" 2>/dev/null || stat -c%s "$1"
}

original_size=$(filesize "$original_font")
subset_size=$(filesize "$subset_font")

reduction=$(awk "BEGIN {printf \"%.3f\", (1 - $subset_size / $original_size) * 100}")
original_mb=$(awk "BEGIN {printf \"%.2f\", $original_size / 1024 / 1024}")
subset_kb=$(awk "BEGIN {printf \"%.2f\", $subset_size / 1024}")
nr_gylphs=$(printf "%s" "$subset" | wc -m | tr -d ' ')

echo
echo "Font subset created!"
echo "  Output:    ${subset_font}"
echo "  Glyphs:    ${nr_gylphs}"
echo "  Original:  ${original_mb} MB"
echo "  Subset:    ${subset_kb} KB"
echo "  Reduction: ${reduction}%"
