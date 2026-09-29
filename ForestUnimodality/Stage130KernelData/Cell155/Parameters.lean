import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell155
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 76
  A := (-16516702741755308514370881/10000000000000000000000000)
  B := (226304600257463128798463/2000000000000000000000000)
  C := (50036935316618768795904337/10000000000000000000000000000)
  dδ := (35091703939936255696174783/500000000000000000000000000)
  dM := (421722192866732538667901/312500000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(31752553044987448238600791/5000000000000000000000000), (14124568309939638410810403/2000000000000000000000000), (3043518262375447847034593/50000000000000000000000)]
  retention := ![(7/10), (3/5), (1/100)]
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
end ForestUnimodality.Stage130KernelData.Cell155
