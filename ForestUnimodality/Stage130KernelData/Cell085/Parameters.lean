import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 75
  A := (-12022466168676676956295069/10000000000000000000000000)
  B := (23553376618442447426593489/250000000000000000000000000)
  C := (22793342796008347200809041/10000000000000000000000000000)
  dδ := (2861164544293217093517967/40000000000000000000000000)
  dM := (18378895337417443939243/16000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(48679044557492527900421919/5000000000000000000000000), (2678195287303263283362753/2500000000000000000000000), (62921426577384785616686713/1000000000000000000000000)]
  retention := ![(7/10), (3/5), (1/1000)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (5381/10506)
  hi := (10787/21012)
  vmin := (110297075/441504144)
  damping := (110297075/441504144)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell085
