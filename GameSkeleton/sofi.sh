#!/bin/bash

# version [2025-03-14]

# PURPOSE:
#
# The purpose of this script is to make it easier to insert new levels and/or
# reorder levels in an existing planet/world, by simply renaming the files in
# such a way that the alphabetical order of the filenames reflects the intended
# order of the levels in the game.
# 
# For example, suppose we have world "Arithmetic" with three levels, and with
# one additional file that is not ready for deployment yet:
#
#     Arithmetic/L01_hello.lean
#     Arithmetic/L02_multiply.lean
#     Arithmetic/L03_add.lean
#     Arithmetic/possible_future_level.lean
#
#  It is mandatory that the file names have the format "L**.lean" or
#  "L**_*****.lean", where "*" are arbitrary symbols other than "_" and ".".  To
#  switch the order of levels L02 and L03 in this example, and to insert an
#  additional level on sustraction between them, use the following steps:
#
# STEP 1: Create a new file for the additional level and rename files as
#    follows:
#
#    Arithmetic/L01_hello.lean
#    Arithmetic/L02a_add.lean              (renamed L03 file)
#    Artihmetic/L02b_substract.lean        (new file)
#    Arithmetic/L03_multiply.lean          (renamed L02 file)
#    Arithmetic/possible_future_level.lean
#
#    The file names should still have the general format specified above. Any
#    part of the filename between "_" and ".lean" will be left intact by the
#    script.  The alphabetical order of the file name should reflect the
#    intended order in the game.
#
# STEP 2:  To any new level, add a least a line
#
#    Level ??"
#
#     There should be no whitespace at the beginning of the line.  The
#     characters "??" are optional -- the script will replace them by the
#     correct level number. Also, in case you'd like to import the previous
#     level, add the line
# 
#     import Game.Levels.Arithmetic.??
#
#     Again, there should be no whitespace at the beginning of the line, and
#     again, the characters ".??" are optional.  The script will replace them
#     with the file name of the previous level.
#
# STEP 3: Execute the script by calling
#
#     $ ./sofi /some_path/Game/Levels/Arithmetic
#
#     The script will rename (renumber) the active level files in their
#     alphabetical order:
#
#     Arithmetic/L01_hello.lean
#     Arithmetic/L02_add.lean               (renamed file)         
#     Artihmetic/L03_substract.lean         (renamed file)
#     Arithmetic/L04_multiply.lean          (renamed file)
#     Arithmetic/possible_future_level.lean
# 
#     Moreover, it will do the following:
#     
#     - Update the level number in each file.
#     
#     - In every level n > 1, replace the first import of a levels from the
#       current world with an import of level n-1. In level n = 1, remove all
#       imports of levels from the current world.
#     
#     - Update the base file for the world, e.g. the file Arithmetic.lean in the
#       above example, to import all active level files.

################################################################################
# Boiler plate code to check that path to a world folder is passed as an
# argument:

if ! [ -n "$1" ]; then
    echo "ERROR: Please specify a world folder." >&2
    exit
fi

path=$(realpath "$1" 2>/dev/null)

if ! ([ -n "$path" ] && [ -e "$path" ]); then
    printf "ERROR: The specified world folder\n    %s\ndoes not exist.\n"  $path >&2
    exit
fi

if ! ([ -d "$path" ]); then
    printf "ERROR: The specified world folder\n    %s\nis not recognized as a folder -- it appears to be a regular file.\n"  $path >&2
    exit
fi

if ! ([ -e "${path}.lean" ]); then
    printf "ERROR: The specified world folder\n    %s\ndoes not have an accompanying file\n    %s\n"  "${path}" "${path}.lean" >&2
    exit
fi

world_path=$(dirname "$path")
world_name=$(basename "$path")
    
#if ! [[ "$world_path" =~ ^(.*)/Game/Levels$ ]]; then
#    printf "ERROR: The specified folder\n    %s\ndoes not look like a world folder.\n" $path >&2
#    printf "World folders are expected to be direct subfolders of\n     '.../Game/Levels/'\n" >&2   
#    exit
#else
printf "%s\n" \
       "This script will make a number of changes to folder" \
       "    ${path}" \
       "and to the associated file" \
       "    ${path}.lean    " \
       "It is recommended that you git commit all local " \
       "changes before running the script.                 "
#fi
read -p "Are you sure you want to proceed?"

################################################################################
# Read names of existing level files and count them:

cd ${world_path}/${world_name}
readarray -t old_names < <(sort < <(find ./L*.lean))
# sort might be superfluous here
# printf '%s\n' "${old_names[@]}"
 
number_of_files=${#old_names[@]}
#echo "$number_of_files"" level files found"

################################################################################
# Rename level files:

echo "Renaming files ..."
new_names=("${old_names[@]}") 
for (( n=0; n<${number_of_files}; n++ ));
do
    old_names[$n]="$(echo ${old_names[$n]} | sed 's,^./,,')" # remove leading ./ in all level names
    old_names[$n]="$(echo ${old_names[$n]} | sed 's,.lean$,,')" # remove trailing .lean in all level names
    temp_name="$(echo ${old_names[$n]} | sed 's,L[^_]*,,')" # temporarily also remove leading L???_
    new_names[$n]="$(printf 'L%02d%s\n' $((n+1)) "${temp_name}")"
    ## Display planned renaming scheme:
    compstr="==="
    [ "${old_names[$n]}" != "${new_names[$n]}" ] && compstr="-->"
    printf "  %-20s %s %s\n" ${old_names[$n]} ${compstr} ${new_names[$n]}
done
#read -p "Proceed with renaming?"

# Need to do renaming in two steps in case some of the new names match some of
# the old names.  For example, the following renaming 
#
# L00.lean --> L01.lean
# L01.lean --> L02.lean
# 
# will not work file by file, because the renamed L00.lean will overwrite the
# existing file L01.lean.  So instead, we create a temporary subfolder
# ./sofi-temp, rename and simultaneously move each file into that folder, and
# then move all files back again.
mkdir "${world_path}/${world_name}/.sofi-temp"
for (( n=0; n<${number_of_files}; n++ ));
do
    mv "${world_path}/${world_name}/${old_names[$n]}.lean" "${world_path}/${world_name}/.sofi-temp/${new_names[$n]}.lean"
done
for (( n=0; n<${number_of_files}; n++ ));
do
    mv "${world_path}/${world_name}/.sofi-temp/${new_names[$n]}.lean" "${world_path}/${world_name}/${new_names[$n]}.lean"
done
rm -d "${world_path}/${world_name}/.sofi-temp"

################################################################################
# Edit the level files -- update level numbers and imports

for (( n=0; n<${number_of_files}; n++ )); #loop over all levels n
do
    FILE="${world_path}/${world_name}/${new_names[$n]}.lean"
    echo "Updating ${FILE} ..."
    # Update "level number":
    echo "   Updating level number ..."
    sed -i "s/^Level.*$/Level $((n+1))/" "$FILE"
    # Replace import of old level k with import of new level k, provided k < n:
    for (( k=0; k<$n; k++));  #loop over all levels k < n
    do
        # echo "replace: import Game.Levels.${world_name}.${old_names[$k]}"
        # echo "by:      import Game.Levels.${world_name}.${new_names[$k]}"
        sed -i "s/^import Game\.Levels\.${world_name}\.${old_names[$k]}[[:space:]]*$/import Game.Levels.${world_name}.${new_names[$k]}/" "$FILE"
    done
    echo "   Updating imports ..."
    # Delete import of old level k if k > n:
    for (( k=$((n+1)); k<${number_of_files}; k++));
    do
        # echo "delete: import Game.Levels.${world_name}.${old_names[$k]}"
        sed -i "s/^import Game.Levels.${world_name}.${old_names[$k]}[[:space:]]*$//" "$FILE"
    done
    # In level 0, delete imports from current world.  In higher levels, replace
    # first import of level from current world with import of level n-1.
    if (( n == 0 )); then
        sed -i "/^import Game\.Levels\.${world_name}.*$/d" "$FILE"
        # Test this sed syntax with:
        # echo -e "import Game.Levels.abc\nQVM\nimport Game.Levels.qvm" | sed "/^import Game\.Levels.*$/d"
    else
        sed -i "0,/^import Game\.Levels\.${world_name}.*$/s/^import Game\.Levels\.${world_name}.*$/import Game.Levels.${world_name}.${new_names[$((n-1))]}/" "$FILE"
        # Test with sed syntax with:
        # echo -e "import Game.Levels.abc\nQVM\nimport Game.Levels.qvm" | sed "0,/^import Game\.Levels\.${world_name}.*$/s/^import Game\.Levels.*$/Super/"
    fi    
done

################################################################################
# Update $world_name.lean file
FILE="${world_path}/${world_name}.lean"
echo "Updating imports in ${FILE} ..."

# delete all existing imports:
sed -i '/^import /d' "$FILE"
new_imports=""
for (( n=0; n<${number_of_files}; n++));
do
    new_imports=$new_imports"import Game.Levels.${world_name}.${new_names[$n]}\n"
done
# add imports of all active levels at beginning of file:
echo -e "$new_imports""$(cat $FILE)" > $FILE

echo "Done."

################################################################################
