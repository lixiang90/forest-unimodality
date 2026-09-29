import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell174
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 4) where
  terms := Finset.univ
  scale := 88
  A := (-16527689804724538424807179/10000000000000000000000000)
  B := (5080392262447646495315823/50000000000000000000000000)
  C := (48723260857190323069865201/10000000000000000000000000000)
  dδ := (62933068999670341292507203/1000000000000000000000000000)
  dM := (545338004870464087420201/500000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(5743875296869063618032669/500000000000000000000000), (25258265295678743456164739/10000000000000000000000000), (6175744772592097753260987/500000000000000000000000), (5992411360812338472214833/100000000000000000000000)]
  retention := ![(7/10), (3/5), (1/20), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (11953/22578)
  hi := (31883/60208)
  vmin := (903085975/3625003264)
  damping := (903085975/3625003264)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell174
