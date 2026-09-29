import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 83
  A := (-643745309842633862125183/500000000000000000000000)
  B := (45774554211089911459620083/500000000000000000000000000)
  C := (-31084239458081060116650951/50000000000000000000000000000)
  dδ := (33588155451199745715751277/500000000000000000000000000)
  dM := (103869465588718001662627/100000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(5251405209361541537305129/500000000000000000000000), (26801444872406559483124511/1000000000000000000000000), (4434170946308475436126173/100000000000000000000000)]
  retention := ![(7/10), (1/20), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (131/264)
  hi := (197/396)
  vmin := (17423/69696)
  damping := (17423/69696)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell064
