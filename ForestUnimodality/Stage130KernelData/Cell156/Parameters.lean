import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell156
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 4) where
  terms := Finset.univ
  scale := 88
  A := (-16098941476011802598122813/10000000000000000000000000)
  B := (3112169562967896825622649/31250000000000000000000000)
  C := (23263353390876955438526519/5000000000000000000000000000)
  dδ := (31458814572542070919780599/500000000000000000000000000)
  dM := (2667947028120407093089439/2500000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(11924684351055169884148199/1000000000000000000000000), (1140187583992536418664443/625000000000000000000000), (3646284405533948724809079/250000000000000000000000), (14499432196588218246802171/250000000000000000000000)]
  retention := ![(7/10), (3/5), (1/20), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (47737/90312)
  hi := (31833/60208)
  vmin := (903261375/3625003264)
  damping := (903261375/3625003264)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell156
