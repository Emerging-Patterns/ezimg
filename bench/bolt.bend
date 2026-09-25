# bench/bolt.bend: how bolt lints the bench driver. The driver is host code
# with no laws of its own, so its law rules are advice; every other group is
# an error, as at the root.
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

# a pure def named by no law
def laws() -> String:
  "warn"
