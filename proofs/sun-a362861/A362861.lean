import SunAntichain

/-- Conjecture 3 in OEIS A362861. -/
theorem conjecture3_A362861 : ¬ SunAntichain.OddBasesConjecture :=
  SunAntichain.refuteA362861

#print axioms conjecture3_A362861
