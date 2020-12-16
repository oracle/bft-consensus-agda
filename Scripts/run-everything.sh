# Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.
#
# Copyright (c) 2020 Oracle and/or its affiliates.
# Licensed under the Universal Permissive License v 1.0 as shown at https://oss.oracle.com/licenses/upl/

# This script runs agda over the Everything.agda file.  If it is given any argument, it first
# generates Everything.agda using the gen-everything.sh script in the same directory.

if [ $# -ne 0 ]
then
    echo "Generating Everything.agda"
    dir=`dirname $0`
    ${dir}/gen-everything.sh
fi

if [ ! -f Everything.agda ]
then
    echo "Everything.agda does not exist.  Rerun with any argument to generate it."
    exit 1
fi

agda --no-main Everything.agda
