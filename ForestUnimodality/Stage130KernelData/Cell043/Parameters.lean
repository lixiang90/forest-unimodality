import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 69
  A := (-3283697598464927793742163/2000000000000000000000000)
  B := (3014667223459224776327403/25000000000000000000000000)
  C := (-32790755154838116709747897/10000000000000000000000000000)
  dδ := (74880934852433495008128261/1000000000000000000000000000)
  dM := (15395848089836830854815197/10000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(13403866159518678102813283/1000000000000000000000000), (3367668323869494884093001/62500000000000000000000)]
  retention := ![(3/5), (1/1000)]
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
end ForestUnimodality.Stage130KernelData.Cell043
