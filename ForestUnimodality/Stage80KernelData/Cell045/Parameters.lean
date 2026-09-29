import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 40
  A := (5757377799859684394689907/2500000000000000000000000)
  B := (-5216763983097130047417167/200000000000000000000000000)
  C := (-4217249168575755088883561/1000000000000000000000000000)
  dδ := (12229328357455962472677413/100000000000000000000000000)
  dM := (13224193404305422880340437/25000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(4359433802666849433471441/625000000000000000000000), (32569413063233582761313301/1000000000000000000000000), (26403779380372931484544097/10000000000000000000000000)]
  retention := ![(4/5), (1/20), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (8999/18624)
  hi := (47/97)
  vmin := (86615375/346853376)
  damping := (86615375/346853376)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell045
