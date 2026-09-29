import ForestUnimodality.TerminalExceptionalBranches

/-! Actual short even path branches have the parameters of one of the
six even-path models. The input is a genuine pendant path construction;
no graph isomorphism or numerical state equality is assumed. -/
namespace ForestUnimodality
open Finset TerminalBlockRecurrence
universe u
variable {V : Type u} [DecidableEq V]

theorem even_path_model_state (j : Fin 6) :
    iterate (2 * j.val + 1) (⟨1, 2, 0, 2, 1, 1, 1⟩ : BlockState ℝ) =
      actualBlockState (MeanTerminalGraphs.branchGraph ⟨j.val + 2, by omega⟩)
        univ (MeanTerminalGraphs.branchRoot ⟨j.val + 2, by omega⟩) := by
  rw [terminal_model_state]
  fin_cases j <;>
    norm_num [iterate, extend, MeanTerminalGraphs.expectedStatistics, MeanTerminalGraphs.branchOrder]

theorem PendantPathExtension.even_branchParameters
    {G : SimpleGraph V} {B : Finset V} {tip root : V} {n : ℕ}
    (hp : PendantPathExtension G {tip} tip n B root)
    (hshort : n + 1 ≤ 13) (heven : (n + 1) % 2 = 0) :
    ∃ i : Fin 8, 2 ≤ i.val ∧ InducedIso.BranchParameters G B root i := by
  let j : Fin 6 := ⟨n / 2, by omega⟩
  have hn : n = 2 * j.val + 1 := by dsimp [j]; omega
  refine ⟨⟨j.val + 2, by omega⟩, ?_, ?_⟩
  · change 2 ≤ j.val + 2
    omega
  apply branchParameters_of_actualBlockState_eq _ hp.endpoint_mem
  rw [hp.actualBlockState_path]
  exact (congrArg (fun k => iterate k (⟨1, 2, 0, 2, 1, 1, 1⟩ : BlockState ℝ)) hn).trans
    (even_path_model_state j)

#print axioms even_path_model_state
#print axioms PendantPathExtension.even_branchParameters
end ForestUnimodality
