import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell186
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 4) where
  terms := Finset.univ
  scale := 88
  A := (-3349067711753127209988179/2000000000000000000000000)
  B := (10255041189769277532040093/100000000000000000000000000)
  C := (24001772748962913600623281/5000000000000000000000000000)
  dδ := (6287410715887764567355589/100000000000000000000000000)
  dM := (5506323521681919701611929/5000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(2246078516531605018258233/200000000000000000000000), (2961380638777365792435603/1000000000000000000000000), (5432748253476824551455593/500000000000000000000000), (61210132663125286001104541/1000000000000000000000000)]
  retention := ![(7/10), (3/5), (1/20), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (7977/15052)
  hi := (95749/180624)
  vmin := (8126696375/32625029376)
  damping := (8126696375/32625029376)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell186
