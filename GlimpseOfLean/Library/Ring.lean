import GlimpseOfLean.Library.Basic
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations

macro "setup" : command =>
`(attribute [-aesop] mul_mem add_mem
attribute [aesop unsafe apply (rule_sets := [SetLike])] mul_mem add_mem Ideal.mul_mem_left Ideal.mul_mem_right)
