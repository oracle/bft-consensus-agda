#! /bin/bash

# Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.
#
# Copyright (c) 2020 Oracle and/or its affiliates.
# Licensed under the Universal Permissive License v 1.0 as shown at https://oss.oracle.com/licenses/upl/

echo "module Everything where" > src/Everything.agda
for f in $(find src -type d -maxdepth 1 -mindepth 1)
do
    find "$f" -name "*.agda" \
      | sed 's/\.agda//' \
      | sed 's/src.//' \
      | sed 's!/!\.!g' \
      | sed 's/^/open import /' >> src/Everything.agda
done


