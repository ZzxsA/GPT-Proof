import CycleCertificate

-- Source c5b13d43, rank 1656: https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/audit_top_normalised.json#L38731-L38753
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private theorem burns_c5b13d43 :
    CycleCertificate.successful 23 [4, 12, 18, 21, 22] = true := by decide

theorem counterexample_c5b13d43 :
    ¬ CycleCertificate.BoundAt 23 (fun k => 3 * k - 4) :=
  CycleCertificate.refute 23 [4, 12, 18, 21, 22] (fun k => 3 * k - 4)
    (by decide) burns_c5b13d43 (by decide)

-- The cycle satisfies the source hypotheses: nontrivial, claw_free, regular.
theorem violates_c5b13d43 :
    CycleCertificate.CycleGraphHypotheses 23 ∧
      ∃ burning cover : Nat,
        CycleCertificate.IsBurningNumber 23 burning ∧
        CycleCertificate.IsCliqueCoverNumber 23 cover ∧
        3 * (burning : Int) - 4 < (cover : Int) := by
  refine ⟨CycleCertificate.cycle_graph_hypotheses (by decide), ?_⟩
  obtain ⟨burning, cover, hb, hc, hgap⟩ :=
    CycleCertificate.exists_optima_violation 23 [4, 12, 18, 21, 22] (fun k => 3 * k - 4)
      (by decide) burns_c5b13d43 (by decide) (by intro x y hxy; omega)
  refine ⟨burning, cover, hb, hc, ?_⟩
  change 3 * burning - 4 < cover at hgap
  omega
