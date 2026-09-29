import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 38
  A := (-10558276355997849915269171/50000000000000000000000000)
  B := (99544973773768336000600243/1000000000000000000000000000)
  C := (60654158530992303630102747/10000000000000000000000000000)
  dδ := (2476305232144747348055347/20000000000000000000000000)
  dM := (285430002760292682480181/125000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(28372102780496435414647749/5000000000000000000000000), (17962078404457837432772749/5000000000000000000000000), (710106459753585639305129/25000000000000000000000)]
  retention := ![(7/10), (1/10), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (7427/14352)
  hi := (11153/21528)
  vmin := (115712375/463454784)
  damping := (115712375/463454784)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell106
