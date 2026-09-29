import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 61
  A := (-87283197893347301942412741/100000000000000000000000000)
  B := (5634458256005724606507723/62500000000000000000000000)
  C := (32900479758451294659549191/10000000000000000000000000000)
  dδ := (3186138913594680488472477/40000000000000000000000000)
  dM := (6353105272924894440095267/5000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(5481836382235230065163023/625000000000000000000000), (51279876384626135177313699/1000000000000000000000000)]
  retention := ![(7/10), (1/100)]
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
end ForestUnimodality.Stage99KernelData.Cell095
