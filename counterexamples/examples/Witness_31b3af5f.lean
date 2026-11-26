import CycleCertificate

-- Source 31b3af5f, rank 2256: https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/audit_top_normalised.json#L52314-L52334
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private theorem burns_31b3af5f :
    CycleCertificate.successful 33 [5, 15, 23, 28, 31, 32] = true := by decide

theorem counterexample_31b3af5f :
    ¬ CycleCertificate.BoundAt 33 (fun k => 3 * k - 2) :=
  CycleCertificate.refute 33 [5, 15, 23, 28, 31, 32] (fun k => 3 * k - 2)
    (by decide) burns_31b3af5f (by decide)

-- The cycle satisfies the source hypotheses: nontrivial, subcubic.
theorem violates_31b3af5f :
    CycleCertificate.CycleGraphHypotheses 33 ∧
      ∃ burning cover : Nat,
        CycleCertificate.IsBurningNumber 33 burning ∧
        CycleCertificate.IsCliqueCoverNumber 33 cover ∧
        3 * (burning : Int) - 2 < (cover : Int) := by
  refine ⟨CycleCertificate.cycle_graph_hypotheses (by decide), ?_⟩
  obtain ⟨burning, cover, hb, hc, hgap⟩ :=
    CycleCertificate.exists_optima_violation 33 [5, 15, 23, 28, 31, 32] (fun k => 3 * k - 2)
      (by decide) burns_31b3af5f (by decide) (by intro x y hxy; omega)
  refine ⟨burning, cover, hb, hc, ?_⟩
  change 3 * burning - 2 < cover at hgap
  omega
