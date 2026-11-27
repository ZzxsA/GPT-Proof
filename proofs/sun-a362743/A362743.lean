import SunAntichain

/-- Conjecture 3 in OEIS A362743. -/
theorem conjecture3_A362743 : ¬ SunAntichain.EvenProductConjecture :=
  SunAntichain.refuteA362743

#print axioms conjecture3_A362743
