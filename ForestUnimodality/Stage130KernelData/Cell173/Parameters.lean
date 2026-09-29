import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell173
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 76
  A := (-16089717937974605155204699/10000000000000000000000000)
  B := (279019411464982922121969/2500000000000000000000000)
  C := (24675000731902534123474169/5000000000000000000000000000)
  dδ := (17614400125975888250495771/250000000000000000000000000)
  dM := (6678539448259640390684333/5000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(71117442997789188652291159/10000000000000000000000000), (2435904361950950303139507/400000000000000000000000), (61124010401188712648945511/1000000000000000000000000)]
  retention := ![(7/10), (3/5), (1/100)]
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
end ForestUnimodality.Stage130KernelData.Cell173
