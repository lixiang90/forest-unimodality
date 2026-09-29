import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell158
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 80
  A := (-7675366478984354989734129/10000000000000000000000000)
  B := (11637043508838504357605359/100000000000000000000000000)
  C := (44962871560137179782756789/100000000000000000000000000)
  dδ := (2138457020421506149521207/20000000000000000000000000)
  dM := (17958950982810010024715019/10000000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(77668009560097184262872361/10000000000000000000000000), (27609457529806263664795551/1000000000000000000000000)]
  retention := ![(7/10), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (643/1188)
  hi := (6/11)
  vmin := (30/121)
  damping := (30/121)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell158
