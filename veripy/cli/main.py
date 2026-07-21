"""
Veripy CLI - Production-ready auto-active verification for Python programs

This module provides the command-line interface for the veripy verification tool,
supporting various verification modes, output formats, and configuration options.

Commands:
-   `verify`: Verify a Python file or directory.
-   `check`: syntax and type checking without full verification.
-   `info`: Display information about the Veripy environment.
-   `version`: Show version information.
"""

import click

from veripy import __version__
from veripy.cli.commands import verify, check, version, info


@click.group()
@click.version_option(version=__version__, prog_name="veripy")
@click.option("--verbose", "-v", is_flag=True, help="Enable verbose output")
@click.option("--quiet", "-q", is_flag=True, help="Suppress all output except errors")
@click.pass_context
def main(ctx: click.Context, verbose: bool, quiet: bool):
    """Veripy - Auto-active verification for Python programs.
    
    A production-ready verification system inspired by Dafny and Verus,
    providing automated verification of Python programs using SMT solving.
    """
    ctx.ensure_object(dict)
    ctx.obj["verbose"] = verbose
    ctx.obj["quiet"] = quiet


# Register all commands
main.add_command(verify)
main.add_command(check)
main.add_command(version)
main.add_command(info)


if __name__ == "__main__":
    main(obj={})
