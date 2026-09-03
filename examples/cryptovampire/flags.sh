#!/usr/bin/env bash
#
# Resolve the invocation flags for ONE .ptcl model.
#
# Each model declares its flags in a first-line pragma:
#
#     /* @cryptovampire run: --exec-pred --pairwise-find-fa timeout=25 */
#
# Tokens (whitespace separated, any order):
#     --exec-pred / --pairwise-find-fa   global flags (injected before `auto`)
#     skip                               model is known not to close at a sane
#                                        timeout -> print SKIP, don't run
#     timeout=N                          per-model solver timeout (seconds)
#
# `-l` (use the lemmas) is always applied to every model: it is a no-op for
# lemma-less models and harmless otherwise (the tool only keeps it off by
# default for legacy reasons).
#
# Prints either "SKIP" or the full argument list to append after the model
# file, e.g. "--exec-pred --pairwise-find-fa auto -l --timeout 20" (global
# flags before the `auto` subcommand, subcommand args after).
#
# Timeout selection: TIMEOUT= env > pragma timeout= > 20s for pairwise-find-fa
# models > 15s default.

set -u
file=${1:?usage: flags.sh <model.ptcl>}

line=$(head -n 1 "$file")
flags=
case "$line" in
    *"@cryptovampire run:"*)
        flags=${line#*"@cryptovampire run:"}
        flags=${flags%%'*/'*}
        ;;
esac

globals=
ptimeout=
for tok in $flags; do
    case "$tok" in
        skip)      echo SKIP; exit 0 ;;
        timeout=*) ptimeout=${tok#timeout=} ;;
        -l)        : ;;               # always on, ignore
        *)         globals="$globals $tok" ;;
    esac
done

t=${TIMEOUT:-$ptimeout}
if [ -z "$t" ]; then
    case " $globals " in
        *" --pairwise-find-fa "*) t=20 ;;
        *)                        t=15 ;;
    esac
fi

printf '%s auto -l --timeout %s\n' "$globals" "$t"
