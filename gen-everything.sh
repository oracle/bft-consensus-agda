#! /bin/bash

echo "module Everything where" > Everything.agda
find LibraBFT/ -name "*.agda" \
  | sed 's/\.agda//' \
  | sed 's!//!/!g' \
  | sed 's!/!\.!g' \
  | sed 's/^/  open import /' >> Everything.agda

  
