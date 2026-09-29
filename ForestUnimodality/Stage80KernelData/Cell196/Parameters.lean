import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell196
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 67
  A := (-37631431765754712714056041/100000000000000000000000000)
  B := (10847659644462975814249717/100000000000000000000000000)
  C := (4523902763634775614498551/10000000000000000000000000)
  dδ := (91995749140501162713357/781250000000000000000000)
  dM := (19560153716905960205596493/10000000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(31866615594495919516759841/5000000000000000000000000), (5783693295681352708470513/250000000000000000000000)]
  retention := ![(7/10), (3/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (6/11)
  hi := (97/177)
  vmin := (7760/31329)
  damping := (7760/31329)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell196
