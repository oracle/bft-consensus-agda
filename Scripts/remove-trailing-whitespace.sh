#!/bin/bash

find . \( -name "*.sh" -o -name "*.agda" \) -type f -print0 | xargs -0 sed -i '' -E "s/[[:space:]]*$//"
