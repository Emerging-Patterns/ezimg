# bolt.bend: how bolt lints this repo. Every rule is an error: the gate must
# see no findings.
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

# a def no quantified law reaches, IO included (`coverage`, L001, is opt-in:
# only its own setting turns it on)
def coverage() -> String:
  "error"

# a law with no binder
def closed() -> String:
  "error"

