#! /bin/bash

# Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.
#
# Copyright (c) 2020 Oracle and/or its affiliates.
# Licensed under the Universal Permissive License v 1.0 as shown at https://oss.oracle.com/licenses/upl/

# This script generates a module that imports every .agda file
# under src, so we can typecheck all files with one command
# (see run-everything.sh)
echo "module Everything where" > tmp.$$
for f in $(find src -name "*.agda")
do
        echo $f                       \
      | sed 's/\.agda//' \
      | sed 's/src.//' \
      | sed 's!/!\.!g' \
      | sed 's/^/open import /' >> tmp.$$
done

# Well, not quite *everything*
grep -v "open import Everything" tmp.$$ > src/Everything.agda
rm tmp.$$

