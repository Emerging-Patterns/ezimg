# bolt.bend: how bolt lints this repo. Every group is an error except the law
# rules, which warn while SPEC.md's requirements are pending: the 85 closed
# laws are retired in the change that lands SPEC.md, and `closed` and `trace`
# turn to error there. See bolt/config.bend for the groups and levels.
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

# a def no quantified law reaches, a law with no binder: advice until the
# closed laws are retired and the quantified ones land
def laws() -> String:
  "warn"

# an @unsafe def a law file reaches
def unsafe() -> String:
  "error"
