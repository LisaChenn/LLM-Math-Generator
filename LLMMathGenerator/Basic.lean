import Mathlib.Data.Rat.Basic  -- Provides rational number definitions and operations

-- Define C as 120 (an exact rational number)
def C : ℚ := 120

-- Define E as 2 times C
def E : ℚ := 2 * C

-- Define C1 as 1.15 times C.
-- Since 1.15 is a decimal, we represent it as the rational number 115/100.
def C1 : ℚ := (115 : ℚ) / 100 * C

-- Define E1 as 2 times C1
def E1 : ℚ := 2 * C1

#eval (C, E, C1, E1)
