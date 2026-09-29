import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell134
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 42
  A := (-3720868189516843851816219/12500000000000000000000000)
  B := (22947291182799603448394521/250000000000000000000000000)
  C := (11873602765157326849321251/2000000000000000000000000000)
  dδ := (11234272723206799315942561/100000000000000000000000000)
  dM := (18843213393339129646530949/10000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(54279728881111211080678913/10000000000000000000000000), (21778916002577872745860077/10000000000000000000000000), (6798014026123438213744521/200000000000000000000000)]
  retention := ![(7/10), (3/5), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (1549/2954)
  hi := (2326/4431)
  vmin := (4896230/19633761)
  damping := (4896230/19633761)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell134
