import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell170
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 96
  A := (26399851602118854054879193/10000000000000000000000000)
  B := (-31797647419713123695395041/10000000000000000000000000000)
  C := (78243502395406783200826339/100000000000000000000000000)
  dδ := (2453071067440192737363347/12500000000000000000000000)
  dM := (2606386486545249976838623/2500000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(23574780291268715437524861/2500000000000000000000000), (8630765587877295974550407/5000000000000000000000000), (276598059163850773511939/7812500000000000000000)]
  retention := ![(4/5), (7/10), (1/10)]
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
end ForestUnimodality.Stage80KernelData.Cell170
