import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 84
  A := (-7479270144788313318073847/5000000000000000000000000)
  B := (49420483962208737460652941/500000000000000000000000000)
  C := (-703345824885022452566119/250000000000000000000000000)
  dδ := (65403722506526096314161123/1000000000000000000000000000)
  dM := (2756248309956960042960139/2500000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(4436687856601158608249591/625000000000000000000000), (48038427490041017975386239/10000000000000000000000000), (7053902231226939534280973/100000000000000000000000)]
  retention := ![(7/10), (3/5), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (4487/9312)
  hi := (8999/18624)
  vmin := (21649775/86713344)
  damping := (21649775/86713344)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell044
