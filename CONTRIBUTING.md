# Contribution Guide

We welcome your contributions! There are multiple ways to contribute, including filing issues with feedback, bugs and suggestions, as well as contributing code.  See [these guidelines](./TODO.md) for suggestions of things to do and our [Style Guide](STYLE.md) for notes on coding conventions, style, warnings and errors.

## Issues

For bugs or suggestions, please file a GitHub issue unless it's security related. When filing a bug, remember that the better written the bug is, the more likely it is to be fixed. If you think you've found a security vulnerability, do not raise a GitHub issue and follow the instructions on our [Security Policy](./SECURITY.md).

## Contributing code

You will need to sign the [Oracle Contributor Agreement](https://www.oracle.com/technetwork/community/oca-486395.html) (OCA).

For pull requests to be accepted, the bottom of your commit message must have
the following line using the name and e-mail address you used for the OCA.

```text
Signed-off-by: Your Name <you@example.org>
```

This can be automatically added to pull requests by committing with:

```text
git commit --signoff
```

Only pull requests from committers who can be verified as having signed the OCA can be accepted.

### Copyright notices

Please include a copyright notice consistent with other files when you introduce a new file, and edit the copyright notice of any file you change to update the list of years, separated by commas and with a comma after the last year, e.g., Copyright (c) 2020, 2021, Oracle and/or its affiliates.

It is not necessary to add your name to copyright notices because you mus sign the Oracle Contributor Agreement before we can accept your contribution.  Arguments against listing all contributors in copyright notices are at the bottom of [this Linux Foundation blog post](https://www.linuxfoundation.org/en/blog/copyright-notices-in-open-source-software-projects).  

### Pull request process

1. Fork this repository
2. Create a branch in your fork to implement your changes. If applicable, we recommend using
the issue number as part of your branch name, e.g. `1234-fixes`
3. Ensure that any documentation is updated with the changes that are required
by your fix.
4. Ensure that your changes have not broken any existing proofs (`./Scripts/run-everything.sh yes` should complete without errors).
5. Update the [list of contributors](README.md#contributors) to include your name if it does not already.
6. Submit a pull request. *Do not leave the pull request blank*. Explain exactly
what your changes are meant to do and provide simple steps on how to validate
your changes. Ensure that you reference the issue you created as well.
7. We will review the pull request before it is merged.

## Code of Conduct

Follow the [Golden Rule](https://en.wikipedia.org/wiki/Golden_Rule). If you'd like more specific guidelines see the [Contributor Covenant Code of Conduct](https://www.contributor-covenant.org/version/1/4/code-of-conduct/).
