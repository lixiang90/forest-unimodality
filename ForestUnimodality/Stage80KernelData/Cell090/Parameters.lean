import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 40
  A := (-20634026985344215448847649/25000000000000000000000000)
  B := (1297898647847402775479253/10000000000000000000000000)
  C := (5397395511648213741254243/5000000000000000000000000000)
  dδ := (1181399482105048165392347/10000000000000000000000000)
  dM := (26048398409780739240493297/10000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(74358428579123336810141609/100000000000000000000000000), (14792261201625325206521211/2500000000000000000000000), (32397099685042853423055931/1000000000000000000000000)]
  retention := ![(7/10), (3/5), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (407/808)
  hi := (51/101)
  vmin := (2550/10201)
  damping := (2550/10201)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell090
