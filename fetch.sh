#!bin/bash

#git remote add carcaram https://github.com/ufmg-smite/carcara.git   ; only need to do this once per clone
git checkout main   # check out the main branch of your fork
git fetch carcaram --tags -f
git merge --ff-only carcaram/main
git push   # updates carcara/main into your fork
git checkout - # go back to previous branch
