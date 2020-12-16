# Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.
#
# Copyright (c) 2020 Oracle and/or its affiliates.
# Licensed under the Universal Permissive License v 1.0 as shown at https://oss.oracle.com/licenses/upl/

# This script deletes all .agdai files, causing all type checking to be repeated when
# run-everything.sh is executed, for example.

find . -name "*.agdai" -exec rm {} \;
