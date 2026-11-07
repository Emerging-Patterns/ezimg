# bolt.bend: how bolt lints this repo. Every rule is an error except
# `coverage`, which warns until the laws exist: the gate must see no errors.
# See bolt/config.bend for the groups and levels.
import Base

# what will fail or blow up
def correctness() -> String:
  "error"

# what is probably a slip
def suspicious() -> String:
  "error"

# comments and whitespace
def style() -> String:
  "error"

# a def no quantified law reaches, IO included: advice while guarantees are
# pending. That rule is `coverage` (L001), which `def coverage()` could also
# set on its own.
def laws() -> String:
  "warn"

# a law with no binder
def closed() -> String:
  "error"

