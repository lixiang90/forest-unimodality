import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell206
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 88
  A := (-8711947413748699303681633/5000000000000000000000000)
  B := (10463420849122838374167799/100000000000000000000000000)
  C := (45074841858878493539020127/10000000000000000000000000000)
  dδ := (61678867877985321666045593/1000000000000000000000000000)
  dM := (11192360634424724282615093/10000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(10752896672069478967159739/1000000000000000000000000), (33869996270584459274743949/10000000000000000000000000), (72060552834430239954599529/1000000000000000000000000)]
  retention := ![(7/10), (3/5), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (32351/60776)
  hi := (48539/91164)
  vmin := (2068974875/8310874896)
  damping := (2068974875/8310874896)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell206
