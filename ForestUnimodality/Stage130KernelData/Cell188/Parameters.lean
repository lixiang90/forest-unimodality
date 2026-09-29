import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell188
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 76
  A := (-1031869977467567798390391/625000000000000000000000)
  B := (11362805949499099611443853/100000000000000000000000000)
  C := (390343597983545120833071/80000000000000000000000000)
  dδ := (70438986717337115361914357/1000000000000000000000000000)
  dM := (13601371566817144556638119/10000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(2093715672974349184531917/312500000000000000000000), (33500346182662918970152077/5000000000000000000000000), (7610437369282355923871819/125000000000000000000000)]
  retention := ![(7/10), (3/5), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (95749/180624)
  hi := (47887/90312)
  vmin := (2031605975/8156257344)
  damping := (2031605975/8156257344)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell188
