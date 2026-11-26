import CycleCertificate

-- Source a1136330, rank 2618: https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/audit_top_normalised.json#L60505-L60525
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private theorem burns_a1136330 :
    CycleCertificate.successful 41 [6, 18, 27, 33, 37, 39, 40] = true := by decide

theorem counterexample_a1136330 :
    ¬ CycleCertificate.BoundAt 41 (fun k => 2 * k + 6) :=
  CycleCertificate.refute 41 [6, 18, 27, 33, 37, 39, 40] (fun k => 2 * k + 6)
    (by decide) burns_a1136330 (by decide)

-- The cycle satisfies the source hypotheses: nontrivial, eulerian.
theorem violates_a1136330 :
    CycleCertificate.CycleGraphHypotheses 41 ∧
      ∃ burning cover : Nat,
        CycleCertificate.IsBurningNumber 41 burning ∧
        CycleCertificate.IsCliqueCoverNumber 41 cover ∧
        2 * (burning : Int) + 6 < (cover : Int) := by
  refine ⟨CycleCertificate.cycle_graph_hypotheses (by decide), ?_⟩
  obtain ⟨burning, cover, hb, hc, hgap⟩ :=
    CycleCertificate.exists_optima_violation 41 [6, 18, 27, 33, 37, 39, 40] (fun k => 2 * k + 6)
      (by decide) burns_a1136330 (by decide) (by intro x y hxy; omega)
  refine ⟨burning, cover, hb, hc, ?_⟩
  change 2 * burning + 6 < cover at hgap
  omega
