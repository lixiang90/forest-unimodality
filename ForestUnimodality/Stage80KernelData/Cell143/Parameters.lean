import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell143
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 39
  A := (3779225868015228808616257/250000000000000000000000000)
  B := (78243345351257848063752931/1000000000000000000000000000)
  C := (7609176462445475189882993/1250000000000000000000000000)
  dδ := (2360051656107232109782501/20000000000000000000000000)
  dM := (18089891711380969626515869/10000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(68055093136307585055533309/10000000000000000000000000), (100305319838165707402311/3125000000000000000000)]
  retention := ![(7/10), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (111/211)
  hi := (23557/44732)
  vmin := (498819475/2000951824)
  damping := (498819475/2000951824)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell143
