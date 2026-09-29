import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell169
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 97
  A := (13431820176977647179938913/5000000000000000000000000)
  B := (-5505234945200124241360129/1250000000000000000000000000)
  C := (316344632889585142265787/400000000000000000000000)
  dδ := (4954085361761560030169349/25000000000000000000000000)
  dM := (10366373037017510057994363/10000000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(95887175716759660559773693/10000000000000000000000000), (679260683500516471156061/400000000000000000000000), (17895391693449589354258933/500000000000000000000000)]
  retention := ![(4/5), (7/10), (1/10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (24257/45582)
  hi := (32351/60776)
  vmin := (919577175/3693722176)
  damping := (919577175/3693722176)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell169
