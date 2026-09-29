import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 76
  A := (-3197239914596727686202371/2500000000000000000000000)
  B := (96686372035694592708132689/1000000000000000000000000000)
  C := (15778049482656759765208943/10000000000000000000000000000)
  dδ := (70188861915308417560588339/1000000000000000000000000000)
  dM := (1166904653083215186518129/1000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(9112520050032102858494909/1000000000000000000000000), (8669172929175313901950517/5000000000000000000000000), (15951537085341715993536127/250000000000000000000000)]
  retention := ![(7/10), (3/5), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (3493/6868)
  hi := (26/51)
  vmin := (650/2601)
  damping := (650/2601)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell079
