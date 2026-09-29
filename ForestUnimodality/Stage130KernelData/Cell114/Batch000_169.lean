import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage130KernelData.Cell114.Parameters
import ForestUnimodality.BinomialMassData.Q109_209.Batch000_049
import ForestUnimodality.BinomialMassData.Q109_209.Batch050_099
import ForestUnimodality.BinomialMassData.Q109_209.Batch100_149
import ForestUnimodality.BinomialMassData.Q109_209.Batch150_199
import ForestUnimodality.BinomialMassData.Q4583_8778.Batch000_049
import ForestUnimodality.BinomialMassData.Q4583_8778.Batch050_099
import ForestUnimodality.BinomialMassData.Q4583_8778.Batch100_149
import ForestUnimodality.BinomialMassData.Q4583_8778.Batch150_199

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree000.table
  base := (889413201496261953027300249/10000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (178)
      previous := (89)
      next := (89)
      square := (618876867516848297445797300000000000000)
      linear := (-31978363779001832759019130000000000000)
      constant := (889413201496261953027300249000000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree000.table
  base := (889413201496261953027300249/10000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (178)
      previous := (89)
      next := (89)
      square := (618876867516848297445797300000000000000)
      linear := (-31978363779001832759019130000000000000)
      constant := (889413201496261953027300249000000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 0 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 0 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel000

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree001.table
  base := (240648453056668337159708295851044708535719/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-29594114746033221184972131200130000000000000)
      constant := (21031611531104876386320472874660797827097483278) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree001.table
  base := (12021304636550727296395960923594186896369/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (3428871138)
      previous := (1714435569)
      next := (1714435569)
      square := (11921623758451521662001873490833300000000000000)
      linear := (-13064585855858307778460157881005830000000000000)
      constant := (9266381326352109173044127808551914416749991257960) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 1 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 1 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel001

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (49951131997237524299/100000000000000000000)
  directionHi := (499511319972375243/1000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree002.table
  base := (277775030320770084433565297595366838450357/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-57791382583835863313197547782730000000000000)
      constant := (12164359601903927638134546264749478870350044117) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree002.table
  base := (69333174565475086812193259543291552491609/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (3428871138)
      previous := (1714435569)
      next := (1714435569)
      square := (11921623758451521662001873490833300000000000000)
      linear := (-25513162225186930192895014615680930000000000000)
      constant := (5355990849421143183272529692609529298936855893956) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 2 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 2 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel002

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49951131997237524299/100000000000000000000)
  centralHi := (499511319972375243/1000000000000000000)
  directionLo := (70641568326381973429/100000000000000000000)
  directionHi := (7064156832638197343/10000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree003.table
  base := (43361765197115399195507439665626578352753/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-85988650421638505441422964365330000000000000)
      constant := (7644702444183248402889673192030228276106415172) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree003.table
  base := (173108499940709583782793581868351386996101/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (380985682)
      previous := (190492841)
      next := (190492841)
      square := (1324624862050169073555763721203700000000000000)
      linear := (-4217970954946172511925541261150670000000000000)
      constant := (373872978496431717438701292219552199833457701269) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 3 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 3 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel003

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70641568326381973429/100000000000000000000)
  centralHi := (7064156832638197343/10000000000000000000)
  directionLo := (1351842164293669383/1562500000000000000)
  directionHi := (86517898514794840513/100000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree004.table
  base := (29410431848700105330851544508315419297191/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-114185918259441147569648380947930000000000000)
      constant := (5259268307760757760787294405413823321282400284) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree004.table
  base := (117402082908067101241180547294152626648909/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (3428871138)
      previous := (1714435569)
      next := (1714435569)
      square := (11921623758451521662001873490833300000000000000)
      linear := (-50410314963844175021764728085031130000000000000)
      constant := (2314835769198722683703035925763492890131088366789) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 4 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 4 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel004

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1351842164293669383/1562500000000000000)
  centralHi := (86517898514794840513/100000000000000000000)
  directionLo := (99902263994475048599/100000000000000000000)
  directionHi := (499511319972375243/500000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree005.table
  base := (85934127177329467913661456666473705109479/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-142383186097243789697873797530530000000000000)
      constant := (3941153006333367557245900105683387912887152199) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree005.table
  base := (42882949615587556967091259374516452310853/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (3428871138)
      previous := (1714435569)
      next := (1714435569)
      square := (11921623758451521662001873490833300000000000000)
      linear := (-62858891333172797436199584819706230000000000000)
      constant := (1734986774121284689705814649108950681290306245626) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 5 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 5 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel005

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99902263994475048599/100000000000000000000)
  centralHi := (499511319972375243/500000000000000000)
  directionLo := (22338825339777588329/20000000000000000000)
  directionHi := (55847063349443970823/50000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree006.table
  base := (16622347416533250574881915232964193970537/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-170580453935046431826099214113130000000000000)
      constant := (3173397562904688604348493683934415827308106788) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree006.table
  base := (66367621136360350157112834996550482874969/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (380985682)
      previous := (190492841)
      next := (190492841)
      square := (1324624862050169073555763721203700000000000000)
      linear := (-8367496411389046650070493506042370000000000000)
      constant := (155264432572676432554339048910723230480614523561) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 6 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 6 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel006

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22338825339777588329/20000000000000000000)
  centralHi := (55847063349443970823/50000000000000000000)
  directionLo := (122354785467641920669/100000000000000000000)
  directionHi := (12235478546764192067/10000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree007.table
  base := (53528730786035808609770825847937964382209/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-198777721772849073954324630695730000000000000)
      constant := (2703578910286992297623704315811188222179271329) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree007.table
  base := (26717997545471860269390277795873353938773/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3931290000000000000000000000000000000000000000
      center := (69976962)
      previous := (34988481)
      next := (34988481)
      square := (243298444050031054326568846751700000000000000)
      linear := (-1790939674935306985001414250797070000000000000)
      constant := (24302890141321449081791980835572381521191781434) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 7 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 7 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel007

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122354785467641920669/100000000000000000000)
  centralHi := (12235478546764192067/10000000000000000000)
  directionLo := (26431654594170320281/20000000000000000000)
  directionHi := (66079136485425800703/50000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree008.table
  base := (11047594611094185303326459289682314245263/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-226974989610651716082550047278330000000000000)
      constant := (2406691981700747134760103125497892674189332412) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree008.table
  base := (44115805803958368101242954261611597764941/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (3428871138)
      previous := (1714435569)
      next := (1714435569)
      square := (11921623758451521662001873490833300000000000000)
      linear := (-100204620441158664679504155023731530000000000000)
      constant := (1060371016759271059434880855536438625068941029061) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 8 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 8 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel008

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26431654594170320281/20000000000000000000)
  centralHi := (66079136485425800703/50000000000000000000)
  directionLo := (141283136652763946859/100000000000000000000)
  directionHi := (7064156832638197343/5000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree009.table
  base := (37024381326727692550736597735393349629591/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-255172257448454358210775463860930000000000000)
      constant := (2219401453780418949455709194309786905170164471) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree009.table
  base := (577525022522616811780989996064483882817/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (380985682)
      previous := (190492841)
      next := (190492841)
      square := (1324624862050169073555763721203700000000000000)
      linear := (-12517021867831920788215445750934070000000000000)
      constant := (108680432221122132485558703298000751441992926272) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 9 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 9 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel009

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141283136652763946859/100000000000000000000)
  centralHi := (7064156832638197343/5000000000000000000)
  directionLo := (74926697995856286449/50000000000000000000)
  directionHi := (149853395991712572899/100000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree010.table
  base := (31269436561922616611028193808082749749251/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-283369525286257000339000880443530000000000000)
      constant := (2108452855810603685902506453866162591797032931) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree010.table
  base := (15607423056131711816949298565072163631769/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (3428871138)
      previous := (1714435569)
      next := (1714435569)
      square := (11921623758451521662001873490833300000000000000)
      linear := (-125101773179815909508373868493081730000000000000)
      constant := (929488316256037732446324368754518002406584089698) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 10 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 10 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel010

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74926697995856286449/50000000000000000000)
  centralHi := (149853395991712572899/100000000000000000000)
  directionLo := (39489837203746535761/25000000000000000000)
  directionHi := (31591869762997228609/20000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree011.table
  base := (26504548865295399874195236578320947780397/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (64258)
      previous := (32129)
      next := (32129)
      square := (223414549173582235377932825300000000000000)
      linear := (-2574932174579005309646498322530000000000000)
      constant := (16987245394725626772181926744303862148723317) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree011.table
  base := (3307016899039569361651500882852861877673/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1592010000000000000000000000000000000000000000
      center := (28337778)
      previous := (14168889)
      next := (14168889)
      square := (98525816185549765801668375957300000000000000)
      linear := (-1136779748340037453907510125849230000000000000)
      constant := (7490786526069118170109021880054997710299354184) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 11 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 11 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel011

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39489837203746535761/25000000000000000000)
  centralHi := (31591869762997228609/20000000000000000000)
  directionLo := (20708645336044101173/12500000000000000000)
  directionHi := (33133832537670561877/20000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree012.table
  base := (4496108378861995090906712333421474251821/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-339764060961862284595451713608730000000000000)
      constant := (2049528692815692472415785636654477083968965505) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree012.table
  base := (11218581125953280724773613314314499199499/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (380985682)
      previous := (190492841)
      next := (190492841)
      square := (1324624862050169073555763721203700000000000000)
      linear := (-16666547324274794926360397995825770000000000000)
      constant := (100447915969266102059806182687274360674264950262) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 12 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 12 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel012

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (20708645336044101173/12500000000000000000)
  centralHi := (33133832537670561877/20000000000000000000)
  directionLo := (6921431881183587241/4000000000000000000)
  directionHi := (86517898514794840513/50000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree013.table
  base := (297468349525079563898000541804543375571/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-367961328799664926723677130191330000000000000)
      constant := (2083704301448499768447454233966702588052278464) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree013.table
  base := (30398307065654060901582559010842814289/16000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (3428871138)
      previous := (1714435569)
      next := (1714435569)
      square := (11921623758451521662001873490833300000000000000)
      linear := (-162447502287801776751678438697107030000000000000)
      constant := (919363952150208858545330347970569097620246105625) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 13 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 13 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel013

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6921431881183587241/4000000000000000000)
  centralHi := (86517898514794840513/50000000000000000000)
  directionLo := (180101367683509842641/100000000000000000000)
  directionHi := (90050683841754921321/50000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree014.table
  base := (25706654910170128372682053472070559633/16000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-396158596637467568851902546773930000000000000)
      constant := (2153170441522119757336507466653166322080670625) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree014.table
  base := (500984900647802739785976764865391822083/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 3931290000000000000000000000000000000000000000
      center := (69976962)
      previous := (34988481)
      next := (34988481)
      square := (243298444050031054326568846751700000000000000)
      linear := (-3569307727696538758492108070036370000000000000)
      constant := (19393166345640105360156974902571561891957366624) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 14 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 14 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel014

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (180101367683509842641/100000000000000000000)
  centralHi := (90050683841754921321/50000000000000000000)
  directionLo := (186900022015183962701/100000000000000000000)
  directionHi := (93450011007591981351/50000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree015.table
  base := (3371323220367214179137590723609224813033/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-424355864475270210980127963356530000000000000)
      constant := (2254375679101909531456426110892348196232377892) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree015.table
  base := (6726847305019468219145575716681506139759/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (380985682)
      previous := (190492841)
      next := (190492841)
      square := (1324624862050169073555763721203700000000000000)
      linear := (-20816072780717669064505350240717470000000000000)
      constant := (110574533962927796227977224478628307229699662142) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 15 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 15 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel015

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186900022015183962701/100000000000000000000)
  centralHi := (93450011007591981351/50000000000000000000)
  directionLo := (48364975587377339457/25000000000000000000)
  directionHi := (193459902349509357829/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree016.table
  base := (1403858616917662122366888553343705499189/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-452553132313072853108353379939130000000000000)
      constant := (2384567843768358948590296444650131199280597672) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree016.table
  base := (1400315270428512534628853057631371328467/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (3428871138)
      previous := (1714435569)
      next := (1714435569)
      square := (11921623758451521662001873490833300000000000000)
      linear := (-199793231395787643994983008901132330000000000000)
      constant := (1052868230171376636806084675883660124563650071256) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 16 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 16 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel016

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48364975587377339457/25000000000000000000)
  centralHi := (193459902349509357829/100000000000000000000)
  directionLo := (99902263994475048599/50000000000000000000)
  directionHi := (199804527988950097199/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree017.table
  base := (1156613818018662853019605745927939236617/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-480750400150875495236578796521730000000000000)
      constant := (2541542052465884155191976461767736510357337416) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree017.table
  base := (1845509711422748415094275900092331255439/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (3428871138)
      previous := (1714435569)
      next := (1714435569)
      square := (11921623758451521662001873490833300000000000000)
      linear := (-212241807765116266409417865635807430000000000000)
      constant := (1122385572111857691302212740637455993059272264595) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 17 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 17 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel017

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99902263994475048599/50000000000000000000)
  centralHi := (199804527988950097199/100000000000000000000)
  directionLo := (205953793343780364553/100000000000000000000)
  directionHi := (102976896671890182277/50000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree018.table
  base := (7510117858976057715618432533396329349681/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-508947667988678137364804213104330000000000000)
      constant := (2723494286493949688126366359602025062323415761) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree018.table
  base := (3743744447216706331184998886714241166361/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (380985682)
      previous := (190492841)
      next := (190492841)
      square := (1324624862050169073555763721203700000000000000)
      linear := (-24965598237160543202650302485609170000000000000)
      constant := (133658616363436971389816091944487957302005854418) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 18 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 18 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel018

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (205953793343780364553/100000000000000000000)
  centralHi := (102976896671890182277/50000000000000000000)
  directionLo := (211924704979145920289/100000000000000000000)
  directionHi := (21192470497914592029/10000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree019.table
  base := (5968265631335537174024453826477377846757/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (21538)
      previous := (10769)
      next := (10769)
      square := (74884100969538643990941473300000000000000)
      linear := (-1487936110322661439038863240130000000000000)
      constant := (8113378262530297817488540571173762719457597) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree019.table
  base := (743516174697320311339234627487689221941/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 533610000000000000000000000000000000000000000
      center := (9498258)
      previous := (4749129)
      next := (4749129)
      square := (33023888527566542000005189725300000000000000)
      linear := (-656894627434275654399688584778830000000000000)
      constant := (3584030705440590094060855222791134676575949608) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 19 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 19 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel019

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211924704979145920289/100000000000000000000)
  centralHi := (21192470497914592029/10000000000000000000)
  directionLo := (54432984122854844891/25000000000000000000)
  directionHi := (43546387298283875913/20000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree020.table
  base := (91975540284381410498724171946679446581/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-565342203664283421621255046269530000000000000)
      constant := (3156599586050161883422809912270745245305233050) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree020.table
  base := (183236178866884689199400089905601823029/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (3428871138)
      previous := (1714435569)
      next := (1714435569)
      square := (11921623758451521662001873490833300000000000000)
      linear := (-249587536873102133652722435839832730000000000000)
      constant := (1394557916067545497275455845340734790379820482725) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 20 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 20 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel020

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54432984122854844891/25000000000000000000)
  centralHi := (43546387298283875913/20000000000000000000)
  directionLo := (22338825339777588329/10000000000000000000)
  directionHi := (223388253397775883291/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree021.table
  base := (422210859152316798489378382713432960777/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-593539471502086063749480462852130000000000000)
      constant := (3405457565288041564673765122986873721277601096) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree021.table
  base := (840465286301536702031354460190377973899/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-594186197828641170220311321030630000000000000)
      constant := (3411869904086959300324717976433783601111528876) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 21 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 21 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel021

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22338825339777588329/10000000000000000000)
  centralHi := (223388253397775883291/100000000000000000000)
  directionLo := (14306552714129477771/6250000000000000000)
  directionHi := (228904843426071644337/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree022.table
  base := (1142423492369768412691070116540036935197/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (64258)
      previous := (32129)
      next := (32129)
      square := (223414549173582235377932825300000000000000)
      linear := (-5138320159833790957666990739130000000000000)
      constant := (30368788396134296873064880745801906667212234) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree022.table
  base := (141929025641652294611002404260080223441/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1592010000000000000000000000000000000000000000
      center := (28337778)
      previous := (14168889)
      next := (14168889)
      square := (98525816185549765801668375957300000000000000)
      linear := (-2268468509188094037037951647183330000000000000)
      constant := (13418821094608881255074668390312654506432490256) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 22 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 22 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel022

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14306552714129477771/6250000000000000000)
  centralHi := (228904843426071644337/100000000000000000000)
  directionLo := (234291576740863266811/100000000000000000000)
  directionHi := (58572894185215816703/25000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree023.table
  base := (1303293757107108542522714508795986382083/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-649934007177691348005931296017330000000000000)
      constant := (3963356091334832620557259507438607481155767523) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree023.table
  base := (8068529258761367594216220482833433867/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (3428871138)
      previous := (1714435569)
      next := (1714435569)
      square := (11921623758451521662001873490833300000000000000)
      linear := (-286933265981088000896027006043858030000000000000)
      constant := (1751359584998159456988925375506666658177966769120) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 23 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 23 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel023

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (234291576740863266811/100000000000000000000)
  centralHi := (58572894185215816703/25000000000000000000)
  directionLo := (119778606728753181527/50000000000000000000)
  directionHi := (47911442691501272611/20000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree024.table
  base := (104683289887538317866610257936654508029/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-678131275015493990134156712599930000000000000)
      constant := (4271031273937677405346148973389244022260858996) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree024.table
  base := (81576468406754960653386806314537716787/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (380985682)
      previous := (190492841)
      next := (190492841)
      square := (1324624862050169073555763721203700000000000000)
      linear := (-33264649150046291478940206975392570000000000000)
      constant := (209711805835099400770218193922585483891708372015) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 24 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 24 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel024

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119778606728753181527/50000000000000000000)
  centralHi := (47911442691501272611/20000000000000000000)
  directionLo := (244709570935283841339/100000000000000000000)
  directionHi := (12235478546764192067/5000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree025.table
  base := (-380885004609614997487819113161294354491/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-706328542853296632262382129182530000000000000)
      constant := (4597122579099680064817763519143751501301478629) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree025.table
  base := (-390418356308487732921986001481798019431/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (3428871138)
      previous := (1714435569)
      next := (1714435569)
      square := (11921623758451521662001873490833300000000000000)
      linear := (-311830418719745245724896719513208230000000000000)
      constant := (2031585506514611948350394855697469149094536409649) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 25 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 25 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel025

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244709570935283841339/100000000000000000000)
  centralHi := (12235478546764192067/5000000000000000000)
  directionLo := (249755659986187621497/100000000000000000000)
  directionHi := (124877829993093810749/50000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree026.table
  base := (-22114440435298210340729652645236638877/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-734525810691099274390607545765130000000000000)
      constant := (4941186151669920447700070966552750918860688150) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree026.table
  base := (-1114084532063607283756635573544825986751/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (3428871138)
      previous := (1714435569)
      next := (1714435569)
      square := (11921623758451521662001873490833300000000000000)
      linear := (-324278995089073868139331576247883330000000000000)
      constant := (2183701879794602969203298831705415239128073739929) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 26 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 26 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel026

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249755659986187621497/100000000000000000000)
  centralHi := (124877829993093810749/50000000000000000000)
  directionLo := (254701796779963071789/100000000000000000000)
  directionHi := (25470179677996307179/10000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree027.table
  base := (-441086912980100947530771586436944181469/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-762723078528901916518832962347730000000000000)
      constant := (5302847655961634541753994683773401364837010444) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree027.table
  base := (-1771672298588927123764271036721629978041/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (380985682)
      previous := (190492841)
      next := (190492841)
      square := (1324624862050169073555763721203700000000000000)
      linear := (-37414174606489165617085159220284270000000000000)
      constant := (260398950355305864254029556774135051565530362871) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 27 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 27 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel027

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254701796779963071789/100000000000000000000)
  centralHi := (25470179677996307179/10000000000000000000)
  directionLo := (129776847772192260769/50000000000000000000)
  directionHi := (259553695544384521539/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree028.table
  base := (-1181995011013271877735669196088776185731/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-790920346366704558647058378930330000000000000)
      constant := (5681791360161499786887144375605332334862168378) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree028.table
  base := (-474079365731099042964435324052505286911/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3931290000000000000000000000000000000000000000
      center := (69976962)
      previous := (34988481)
      next := (34988481)
      square := (243298444050031054326568846751700000000000000)
      linear := (-7126043833219002305473495708514970000000000000)
      constant := (51247194663977596310270581729930273245309827405) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 28 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 28 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel028

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (129776847772192260769/50000000000000000000)
  centralHi := (259553695544384521539/100000000000000000000)
  directionLo := (264316545941703202811/100000000000000000000)
  directionHi := (66079136485425800703/25000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree029.table
  base := (-727686490103250602622489310132298637141/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-819117614204507200775283795512930000000000000)
      constant := (6077750948711247780580709810605114252924175916) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree029.table
  base := (-364542850002076752805423288370426123417/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (3428871138)
      previous := (1714435569)
      next := (1714435569)
      square := (11921623758451521662001873490833300000000000000)
      linear := (-361624724197059735382636146451908630000000000000)
      constant := (2686150624705307867751007309809013237422661697144) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 29 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 29 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel029

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264316545941703202811/100000000000000000000)
  centralHi := (66079136485425800703/25000000000000000000)
  directionLo := (4203048095438340089/1562500000000000000)
  directionHi := (268995078108053765697/100000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree030.table
  base := (-3409758201786537228038191695460374291473/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-847314882042309842903509212095530000000000000)
      constant := (6490501781816152649662726141736495390574167887) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree030.table
  base := (-1707320831495731460291807094233207041917/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (380985682)
      previous := (190492841)
      next := (190492841)
      square := (1324624862050169073555763721203700000000000000)
      linear := (-41563700062932039755230111465175970000000000000)
      constant := (318733995881586202132491607306997679753798305254) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 30 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 30 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel030

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4203048095438340089/1562500000000000000)
  centralHi := (268995078108053765697/100000000000000000000)
  directionLo := (136796808839025364797/50000000000000000000)
  directionHi := (54718723535610145919/20000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree031.table
  base := (-773072952239101156373423216926990779759/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-875512149880112485031734628678130000000000000)
      constant := (6919854370640887086954172691292790578746735605) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree031.table
  base := (-3869621039353457003604492212697126063689/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (3428871138)
      previous := (1714435569)
      next := (1714435569)
      square := (11921623758451521662001873490833300000000000000)
      linear := (-386521876935716980211505859921258830000000000000)
      constant := (3058395188854418189298576566331735214857692348831) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 31 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 31 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel031

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (136796808839025364797/50000000000000000000)
  centralHi := (54718723535610145919/20000000000000000000)
  directionLo := (69529033154309376209/25000000000000000000)
  directionHi := (278116132617237504837/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree032.table
  base := (-856244977291146900454013761365081328199/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-903709417717915127159960045260730000000000000)
      constant := (7365648875581607978153406144677219412514697405) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree032.table
  base := (-4284930671469685247591081366535514907013/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (3428871138)
      previous := (1714435569)
      next := (1714435569)
      square := (11921623758451521662001873490833300000000000000)
      linear := (-398970453305045602625940716655933930000000000000)
      constant := (3255447996306950443287575758420435878445923429827) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 32 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 32 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel032

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69529033154309376209/25000000000000000000)
  centralHi := (278116132617237504837/100000000000000000000)
  directionLo := (282566273305527893719/100000000000000000000)
  directionHi := (7064156832638197343/2500000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree033.table
  base := (-1165106319981634658560495164657926771817/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (64258)
      previous := (32129)
      next := (32129)
      square := (223414549173582235377932825300000000000000)
      linear := (-7701708145088576605687483155730000000000000)
      constant := (64692152614814529537552090328623953741496252) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree033.table
  base := (-4663648620394157968432597778809572580953/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 176890000000000000000000000000000000000000000
      center := (3148642)
      previous := (1574321)
      next := (1574321)
      square := (10947312909505529533518708439700000000000000)
      linear := (-377795252226238957796488129835270000000000000)
      constant := (3176956006991489056113073160056097470615522383) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 33 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 33 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel033

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (282566273305527893719/100000000000000000000)
  centralHi := (7064156832638197343/2500000000000000000)
  directionLo := (143473703511810598943/50000000000000000000)
  directionHi := (286947407023621197887/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree034.table
  base := (-5005569689307253744354148065413196074607/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-960103953393520411416410878425930000000000000)
      constant := (8306045408770482697741962247395506182265091633) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree034.table
  base := (-5008370818846125062299646233475300717399/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (3428871138)
      previous := (1714435569)
      next := (1714435569)
      square := (11921623758451521662001873490833300000000000000)
      linear := (-423867606043702847454810430125284130000000000000)
      constant := (3671116468489496292128108274256217906709212777921) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 34 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 34 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel034

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (143473703511810598943/50000000000000000000)
  centralHi := (286947407023621197887/100000000000000000000)
  directionLo := (227548943569499891/78125000000000000)
  directionHi := (291262647768959860481/100000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree035.table
  base := (-132971361889260004047277771763018464107/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-988301221231323053544636295008530000000000000)
      constant := (8800437763471741188744406112675833618773685320) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree035.table
  base := (-166290206002883288086395619396273774483/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 3931290000000000000000000000000000000000000000
      center := (69976962)
      previous := (34988481)
      next := (34988481)
      square := (243298444050031054326568846751700000000000000)
      linear := (-8904411885980234078964189527754270000000000000)
      constant := (79380407209364472064273417059577043193960726176) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 35 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 35 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel035

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (227548943569499891/78125000000000000)
  centralHi := (291262647768959860481/100000000000000000000)
  directionLo := (36939360268974657931/12500000000000000000)
  directionHi := (295514882151797263449/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree036.table
  base := (-1400533088732984642868545769225712865479/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-1016498489069125695672861711591130000000000000)
      constant := (9310846601999304168386190908641686545292047204) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree036.table
  base := (-5604242347398810598099851296587798176519/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (380985682)
      previous := (190492841)
      next := (190492841)
      square := (1324624862050169073555763721203700000000000000)
      linear := (-49862750975817788031520015954959370000000000000)
      constant := (457248886442883770734128563843113491004722204489) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 36 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 36 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel036

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (36939360268974657931/12500000000000000000)
  centralHi := (295514882151797263449/100000000000000000000)
  directionLo := (299706791983425145797/100000000000000000000)
  directionHi := (149853395991712572899/50000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree037.table
  base := (-1464241541631177434558452610843133193959/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-1044695756906928337801087128173730000000000000)
      constant := (9837203657977010019205653634102354395818707684) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree037.table
  base := (-1171759057311697649661917533556888351969/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (3428871138)
      previous := (1714435569)
      next := (1714435569)
      square := (11921623758451521662001873490833300000000000000)
      linear := (-461213335151688714698115000329309430000000000000)
      constant := (4347886545792785631910296659212742499574300854755) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 37 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 37 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel037

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (299706791983425145797/100000000000000000000)
  centralHi := (149853395991712572899/50000000000000000000)
  directionLo := (37980109257347110921/12500000000000000000)
  directionHi := (303840874058776887369/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree038.table
  base := (-1521168556752142105026275645736833664579/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (21538)
      previous := (10769)
      next := (10769)
      square := (74884100969538643990941473300000000000000)
      linear := (-2972002838628063656313885165530000000000000)
      constant := (28751942786744708103937481346403372506343764) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree038.table
  base := (-3043129352411375343877515273143518414781/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 533610000000000000000000000000000000000000000
      center := (9498258)
      previous := (4749129)
      next := (4749129)
      square := (33023888527566542000005189725300000000000000)
      linear := (-1312082857398939992001523149761730000000000000)
      constant := (12707906809560547677233702880133767427737742118) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 38 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 38 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel038

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37980109257347110921/12500000000000000000)
  centralHi := (303840874058776887369/100000000000000000000)
  directionLo := (7697986438698067267/2500000000000000000)
  directionHi := (307919457547922690681/100000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree039.table
  base := (-6286368588735661364140118292794388890993/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-1101090292582533622057537961338930000000000000)
      constant := (10937541090553998865275541324170418298852534767) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree039.table
  base := (-1571935048592271230229282815040579085387/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (380985682)
      previous := (190492841)
      next := (190492841)
      square := (1324624862050169073555763721203700000000000000)
      linear := (-54012276432260662169664968199851070000000000000)
      constant := (537135786606446461575524701368526473134357248788) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 39 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 39 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel039

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7697986438698067267/2500000000000000000)
  centralHi := (307919457547922690681/100000000000000000000)
  directionLo := (77986179835120630537/25000000000000000000)
  directionHi := (311944719340482522149/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree040.table
  base := (-323149365596341935482126686313425259017/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-1129287560420336264185763377921530000000000000)
      constant := (11511431916185980783533061430404065425217568460) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree040.table
  base := (-6464173863813815726197672148249705211667/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (3428871138)
      previous := (1714435569)
      next := (1714435569)
      square := (11921623758451521662001873490833300000000000000)
      linear := (-498559064259674581941419570533334730000000000000)
      constant := (5087871715378641829958755976812892540352285633893) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 40 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 40 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel040

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (77986179835120630537/25000000000000000000)
  centralHi := (311944719340482522149/100000000000000000000)
  directionLo := (39489837203746535761/12500000000000000000)
  directionHi := (315918697629972286089/100000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree041.table
  base := (-661532168749504458724692489516839683699/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-1157484828258138906313988794504130000000000000)
      constant := (12101089258532417067723742169981179257763439810) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree041.table
  base := (-1323269502221630309299031074229986032813/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (3428871138)
      previous := (1714435569)
      next := (1714435569)
      square := (11921623758451521662001873490833300000000000000)
      linear := (-511007640629003204355854427268009830000000000000)
      constant := (5348488090408411468245003715677907536122033240135) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 41 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 41 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel041

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39489837203746535761/12500000000000000000)
  centralHi := (315918697629972286089/100000000000000000000)
  directionLo := (319843303978719090761/100000000000000000000)
  directionHi := (159921651989359545381/50000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree042.table
  base := (-6744039200568439813956908672614875782327/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-1185682096095941548442214211086730000000000000)
      constant := (12706483961175424525200048554266969610952174313) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree042.table
  base := (-337246277015166121595329061601586246711/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-1186975548749051761383875927443730000000000000)
      constant := (12734826317276223410745126827516432223148336180) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 42 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 42 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel042

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (319843303978719090761/100000000000000000000)
  centralHi := (159921651989359545381/50000000000000000000)
  directionLo := (323720334066040327533/100000000000000000000)
  directionHi := (161860167033020163767/50000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree043.table
  base := (-856212862642116754811984777255183274813/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-1213879363933744190570439627669330000000000000)
      constant := (13327591429528393912596094046664220714983146776) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree043.table
  base := (-6850468288839331576233327956686165498509/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (3428871138)
      previous := (1714435569)
      next := (1714435569)
      square := (11921623758451521662001873490833300000000000000)
      linear := (-535904793367660449184724140737360030000000000000)
      constant := (5890571867949875897876326463577585787743096111611) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 43 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 43 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel043

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (323720334066040327533/100000000000000000000)
  centralHi := (161860167033020163767/50000000000000000000)
  directionLo := (81887869322794919467/25000000000000000000)
  directionHi := (327551477291179677869/100000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree044.table
  base := (-6932787743969069329383883010069771950957/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (64258)
      previous := (32129)
      next := (32129)
      square := (223414549173582235377932825300000000000000)
      linear := (-10265096130343362253707975572330000000000000)
      constant := (115408189397455211105924416247084812325704523) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree044.table
  base := (-1386689665517072357434988941426740470107/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1592010000000000000000000000000000000000000000
      center := (28337778)
      previous := (14168889)
      next := (14168889)
      square := (98525816185549765801668375957300000000000000)
      linear := (-4531846030884207203298834689851530000000000000)
      constant := (51008424572043365884510600219364827452092477465) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 44 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 44 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel044

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (81887869322794919467/25000000000000000000)
  centralHi := (327551477291179677869/100000000000000000000)
  directionLo := (331338325376705618769/100000000000000000000)
  directionHi := (33133832537670561877/10000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree045.table
  base := (-1748423592997254835038449882399114179667/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-1270273899609349474826890460834530000000000000)
      constant := (14616864923382913589502359934404047174071863092) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree045.table
  base := (-1748566051948520380493361737203530597117/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (380985682)
      previous := (190492841)
      next := (190492841)
      square := (1324624862050169073555763721203700000000000000)
      linear := (-62311327345146410445954872689634470000000000000)
      constant := (717821471588912615776504633470410065677517135308) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 45 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 45 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel045

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (331338325376705618769/100000000000000000000)
  centralHi := (33133832537670561877/10000000000000000000)
  directionLo := (67016476019332764987/20000000000000000000)
  directionHi := (41885297512082978117/12500000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree046.table
  base := (-7032760743110146210508274686999500804927/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-1298471167447152116955115877417130000000000000)
      constant := (15284998686061279478028259432492354805339983713) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree046.table
  base := (-879156506857765552518185127563587924037/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (3428871138)
      previous := (1714435569)
      next := (1714435569)
      square := (11921623758451521662001873490833300000000000000)
      linear := (-573250522475646316428028710941385330000000000000)
      constant := (6755687006307363101647196244381806693260413224984) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 46 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 46 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel046

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67016476019332764987/20000000000000000000)
  centralHi := (41885297512082978117/12500000000000000000)
  directionLo := (169392530117956009789/50000000000000000000)
  directionHi := (338785060235912019579/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree047.table
  base := (-1762567984484371054378031736726555929187/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-1326668435284954759083341293999730000000000000)
      constant := (15968779752521269707138084524808799241828730612) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree047.table
  base := (-1410139069230588397588969500456067027913/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (3428871138)
      previous := (1714435569)
      next := (1714435569)
      square := (11921623758451521662001873490833300000000000000)
      linear := (-585699098844974938842463567676060430000000000000)
      constant := (7057895198523247550968845787943754782218979604635) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 47 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 47 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel047

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (169392530117956009789/50000000000000000000)
  centralHi := (338785060235912019579/100000000000000000000)
  directionLo := (342447707872101228777/100000000000000000000)
  directionHi := (171223853936050614389/50000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree048.table
  base := (-880808554119973091221224574729599287179/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-1354865703122757401211566710582330000000000000)
      constant := (16668197618509379128299824655110530988293872808) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree048.table
  base := (-704683315731331503653656209226235345993/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (380985682)
      previous := (190492841)
      next := (190492841)
      square := (1324624862050169073555763721203700000000000000)
      linear := (-66460852801589284584099824934526170000000000000)
      constant := (818557023950771074285708694506261478787323085830) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 48 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 48 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel048

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (342447707872101228777/100000000000000000000)
  centralHi := (171223853936050614389/50000000000000000000)
  directionLo := (346071594059179362051/100000000000000000000)
  directionHi := (86517898514794840513/25000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree049.table
  base := (-7021553079320004659666538615817211929853/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-1383062970960560043339792127164930000000000000)
      constant := (17383243423284832240623579500789758365692091107) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree049.table
  base := (-3510933558482043389750326941112540733647/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3931290000000000000000000000000000000000000000
      center := (69976962)
      previous := (34988481)
      next := (34988481)
      square := (243298444050031054326568846751700000000000000)
      linear := (-12461147991502697625945577166232870000000000000)
      constant := (156796677007583538047774081074193715947844177074) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 49 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 49 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel049

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (346071594059179362051/100000000000000000000)
  centralHi := (86517898514794840513/25000000000000000000)
  directionLo := (21853620248791416881/6250000000000000000)
  directionHi := (349657923980662670097/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree050.table
  base := (-1743924247422219806395179594705590557617/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-1411260238798362685468017543747530000000000000)
      constant := (18113909692475058659035363683771160395410927292) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree050.table
  base := (-3487983636036522714690420993816215315611/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (3428871138)
      previous := (1714435569)
      next := (1714435569)
      square := (11921623758451521662001873490833300000000000000)
      linear := (-623044827952960806085768137880085730000000000000)
      constant := (8005963796297883057279255066326153708740537991738) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 50 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 50 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel050

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21853620248791416881/6250000000000000000)
  centralHi := (349657923980662670097/100000000000000000000)
  directionLo := (353207841631909867149/100000000000000000000)
  directionHi := (7064156832638197343/2000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree051.table
  base := (-863630563009912645885553202461852261737/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-1439457506636165327596242960330130000000000000)
      constant := (18860190121163955215777928752434440650840528824) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree051.table
  base := (-172731925865757585106354686011156433661/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (380985682)
      previous := (190492841)
      next := (190492841)
      square := (1324624862050169073555763721203700000000000000)
      linear := (-70610378258032158722244777179417870000000000000)
      constant := (926198924638289773672316544692562854609657563640) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 51 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 51 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel051

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (353207841631909867149/100000000000000000000)
  centralHi := (7064156832638197343/2000000000000000000)
  directionLo := (71344486816593689081/20000000000000000000)
  directionHi := (178361217041484222703/50000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree052.table
  base := (-213178668084688894834862420905796474603/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-1467654774473967969724468376912730000000000000)
      constant := (19622079390918129637181627074980004934171723424) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree052.table
  base := (-6821917353522191653208154912404388236571/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (3428871138)
      previous := (1714435569)
      next := (1714435569)
      square := (11921623758451521662001873490833300000000000000)
      linear := (-647941980691618050914637851349435930000000000000)
      constant := (8672514419834546096071204991308382647590308887709) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 52 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 52 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel052

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (71344486816593689081/20000000000000000000)
  centralHi := (178361217041484222703/50000000000000000000)
  directionLo := (360202735367019685283/100000000000000000000)
  directionHi := (90050683841754921321/25000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree053.table
  base := (-1678454579870056787530660896741872600781/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-1495852042311770611852693793495330000000000000)
      constant := (20399573015441202570783334469037463051701140556) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree053.table
  base := (-3356995116480602321455504943240768842249/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (3428871138)
      previous := (1714435569)
      next := (1714435569)
      square := (11921623758451521662001873490833300000000000000)
      linear := (-660390557060946673329072708084111030000000000000)
      constant := (9016134125627808823218168735040342619009918302142) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 53 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 53 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel053

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (360202735367019685283/100000000000000000000)
  centralHi := (90050683841754921321/25000000000000000000)
  directionLo := (363649730033845426521/100000000000000000000)
  directionHi := (181824865016922713261/50000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree054.table
  base := (-1317086792519294617387470507432503292867/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-1524049310149573253980919210077930000000000000)
      constant := (21192667210377032457318440778363624118321382865) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree054.table
  base := (-1646395424955314852415009487320881603031/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (380985682)
      previous := (190492841)
      next := (190492841)
      square := (1324624862050169073555763721203700000000000000)
      linear := (-74759903714475032860389729424309570000000000000)
      constant := (1040738642440123250454908541082831597856808566244) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 54 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 54 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel054

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (363649730033845426521/100000000000000000000)
  centralHi := (181824865016922713261/50000000000000000000)
  directionLo := (45883044550365720251/12500000000000000000)
  directionHi := (367064356402925762009/100000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree055.table
  base := (-3218318694425540500920986193977262465227/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (64258)
      previous := (32129)
      next := (32129)
      square := (223414549173582235377932825300000000000000)
      linear := (-12828484115598147901728467988930000000000000)
      constant := (181829411433748189285392634091598416500106106) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree055.table
  base := (-3218382153098265540651614382307210687689/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1592010000000000000000000000000000000000000000
      center := (28337778)
      previous := (14168889)
      next := (14168889)
      square := (98525816185549765801668375957300000000000000)
      linear := (-5663534791732263786429276211185630000000000000)
      constant := (80364082572232793975051880424175769502618447022) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 55 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 55 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel055

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (45883044550365720251/12500000000000000000)
  centralHi := (367064356402925762009/100000000000000000000)
  directionLo := (370447509546628688467/100000000000000000000)
  directionHi := (92611877386657172117/25000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree056.table
  base := (-1253498048903203450858523273767876649409/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-1580443845825178538237370043243130000000000000)
      constant := (22825645041989892146878135827219206900385827355) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree056.table
  base := (-313379961999103303306857785758594593749/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3931290000000000000000000000000000000000000000
      center := (69976962)
      previous := (34988481)
      next := (34988481)
      square := (243298444050031054326568846751700000000000000)
      linear := (-14239516044263929399436270985472170000000000000)
      constant := (205884726015977993481766464561402709319080987580) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 56 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 56 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel056

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (370447509546628688467/100000000000000000000)
  centralHi := (92611877386657172117/25000000000000000000)
  directionLo := (186900022015183962701/50000000000000000000)
  directionHi := (373800044030367925403/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree057.table
  base := (-3039022265200759096871540278286102862557/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (21538)
      previous := (10769)
      next := (10769)
      square := (74884100969538643990941473300000000000000)
      linear := (-4456069566933465873588907090930000000000000)
      constant := (65555467353043557488572938554964763107261206) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree057.table
  base := (-121562762097439269285553706116448253047/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 59290000000000000000000000000000000000000000
      center := (1055362)
      previous := (527681)
      next := (527681)
      square := (3669320947507393555556132191700000000000000)
      linear := (-218585676373733814400373079416070000000000000)
      constant := (3219310415060278813850006615149118915384216850) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 57 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 57 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel057

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186900022015183962701/50000000000000000000)
  centralHi := (373800044030367925403/100000000000000000000)
  directionLo := (75424555286699687939/20000000000000000000)
  directionHi := (23570173527093652481/6250000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree058.table
  base := (-5868344110998189558495377318448964410883/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-1636838381500783822493820876408330000000000000)
      constant := (24520992884815213073767823496236770785568219677) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree058.table
  base := (-5868424421554467133554969334465152465071/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (3428871138)
      previous := (1714435569)
      next := (1714435569)
      square := (11921623758451521662001873490833300000000000000)
      linear := (-722633438907589785401246991757486530000000000000)
      constant := (10837617044130952845397961141095873094751396039209) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 58 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 58 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel058

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (75424555286699687939/20000000000000000000)
  centralHi := (23570173527093652481/6250000000000000000)
  directionLo := (380416487672019668667/100000000000000000000)
  directionHi := (95104121918004917167/25000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree059.table
  base := (-88100406054660709269177836048666669217/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-1665035649338586464622046292990930000000000000)
      constant := (25392050936840279759131539609464294238203662272) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree059.table
  base := (-704811861721636202099843701536636391071/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (3428871138)
      previous := (1714435569)
      next := (1714435569)
      square := (11921623758451521662001873490833300000000000000)
      linear := (-735082015276918407815681848492161630000000000000)
      constant := (11222583384547249434424370144081758209508142345672) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 59 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 59 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel059

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (380416487672019668667/100000000000000000000)
  centralHi := (95104121918004917167/25000000000000000000)
  directionLo := (383681925141804587163/100000000000000000000)
  directionHi := (95920481285451146791/25000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree060.table
  base := (-5388321371639594532246572621728754310539/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-1693232917176389106750271709573530000000000000)
      constant := (26278696507164005955394594146022066282961345941) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree060.table
  base := (-5388380476082974239530952247364588062897/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (380985682)
      previous := (190492841)
      next := (190492841)
      square := (1324624862050169073555763721203700000000000000)
      linear := (-83058954627360781136679633914092970000000000000)
      constant := (1290493107054689277244151349602148204012405211007) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 60 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 60 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel060

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (383681925141804587163/100000000000000000000)
  centralHi := (95920481285451146791/25000000000000000000)
  directionLo := (48364975587377339457/12500000000000000000)
  directionHi := (386919804699018715657/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree061.table
  base := (-1279514147883802061991117052657183289833/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-1721430185014191748878497126156130000000000000)
      constant := (27180928445748083722686779607881156306867218908) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree061.table
  base := (-5118107274363124814195978318773235474119/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (3428871138)
      previous := (1714435569)
      next := (1714435569)
      square := (11921623758451521662001873490833300000000000000)
      linear := (-759979168015575652644551561961511830000000000000)
      constant := (12013180278079887790117596855469273718853458510801) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 61 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 61 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel061

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48364975587377339457/12500000000000000000)
  centralHi := (386919804699018715657/100000000000000000000)
  directionLo := (3121046499940759107/800000000000000000)
  directionHi := (48766351561574361047/12500000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree062.table
  base := (-241382692788832401662377916731681253753/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-1749627452851994391006722542738730000000000000)
      constant := (28098745782499026810678194842694928623096304140) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree062.table
  base := (-2413848652640044830063191494916015781133/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (3428871138)
      previous := (1714435569)
      next := (1714435569)
      square := (11921623758451521662001873490833300000000000000)
      linear := (-772427744384904275058986418696186930000000000000)
      constant := (12418809904196187248947760755370472149933938554614) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 62 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 62 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel062

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3121046499940759107/800000000000000000)
  centralHi := (48766351561574361047/12500000000000000000)
  directionLo := (78663121332410317277/20000000000000000000)
  directionHi := (196657803331025793193/50000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree063.table
  base := (-225856594899245107146531895950741315089/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-1777824720689797033134947959321330000000000000)
      constant := (29032147699113536831409401173332603372311947820) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree063.table
  base := (-2258584568397828662184429419915146886379/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-1779764899669462352547440533856830000000000000)
      constant := (29095978422132638601296983684761362937712157802) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 63 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 63 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel063

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (78663121332410317277/20000000000000000000)
  centralHi := (196657803331025793193/50000000000000000000)
  directionLo := (396474818912554804217/100000000000000000000)
  directionHi := (198237409456277402109/50000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree064.table
  base := (-4186506520514496213886984695757869326719/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-1806021988527599675263173375903930000000000000)
      constant := (29981133505328965750536136955183320509939587361) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree064.table
  base := (-2093269214175375565791171328527612032131/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (3428871138)
      previous := (1714435569)
      next := (1714435569)
      square := (11921623758451521662001873490833300000000000000)
      linear := (-797324897123561519887856132165537130000000000000)
      constant := (13250729716319969726250931689425655024123196465898) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 64 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 64 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel064

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (396474818912554804217/100000000000000000000)
  centralHi := (198237409456277402109/50000000000000000000)
  directionLo := (99902263994475048599/25000000000000000000)
  directionHi := (399609055977900194397/100000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree065.table
  base := (-958947763272281077022813123802296708783/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-1834219256365402317391398792486530000000000000)
      constant := (30945702618889652887737287334283717509854599108) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree065.table
  base := (-1917909193219669324349562899899650242963/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (3428871138)
      previous := (1714435569)
      next := (1714435569)
      square := (11921623758451521662001873490833300000000000000)
      linear := (-809773473492890142302290988900212230000000000000)
      constant := (13677019346273682976379240695007840039164151479754) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 65 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 65 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel065

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99902263994475048599/25000000000000000000)
  centralHi := (399609055977900194397/100000000000000000000)
  directionLo := (402718900981011837973/100000000000000000000)
  directionHi := (201359450490505918987/50000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree066.table
  base := (-3464996739678662113350402002542111402877/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (64258)
      previous := (32129)
      next := (32129)
      square := (223414549173582235377932825300000000000000)
      linear := (-15391872100852933549748960405530000000000000)
      constant := (263850037592130166141270714553262297783561403) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree066.table
  base := (-1732510074412453417608775408990210754883/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 176890000000000000000000000000000000000000000
      center := (3148642)
      previous := (1574321)
      next := (1574321)
      square := (10947312909505529533518708439700000000000000)
      linear := (-755024839175591152173301970279970000000000000)
      constant := (12957020348458512490520446510761514323913749226) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 66 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 66 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel066

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (402718900981011837973/100000000000000000000)
  centralHi := (201359450490505918987/50000000000000000000)
  directionLo := (405804914700597809229/100000000000000000000)
  directionHi := (40580491470059780923/10000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree067.table
  base := (-48033329138202061043045669326991580717/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-1890613792041007601647849625651730000000000000)
      constant := (32921588880308112437719954658111381568812846272) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree067.table
  base := (-3074153108576297456146260453355840812947/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (3428871138)
      previous := (1714435569)
      next := (1714435569)
      square := (11921623758451521662001873490833300000000000000)
      linear := (-834670626231547387131160702369562430000000000000)
      constant := (14550256974971180829625940302151212121195300983013) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 67 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 67 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel067

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (405804914700597809229/100000000000000000000)
  centralHi := (40580491470059780923/10000000000000000000)
  directionLo := (10221690918793869937/2500000000000000000)
  directionHi := (408867636751754797481/100000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree068.table
  base := (-20806312726773096798617445386650262599/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-1918811059878810243776075042234330000000000000)
      constant := (33932905264403562940973392244839653424564874368) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree068.table
  base := (-1331612593674533922129206232825460763903/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (3428871138)
      previous := (1714435569)
      next := (1714435569)
      square := (11921623758451521662001873490833300000000000000)
      linear := (-847119202600876009545595559104237530000000000000)
      constant := (14997204640175871306391649692694378564664062596274) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 68 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 68 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel068

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10221690918793869937/2500000000000000000)
  centralHi := (408867636751754797481/100000000000000000000)
  directionLo := (411907586687560729107/100000000000000000000)
  directionHi := (102976896671890182277/25000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree069.table
  base := (-69757136898582752546729565464568444701/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-1947008327716612885904300458816930000000000000)
      constant := (34959803406151566504166641479576019944544499808) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree069.table
  base := (-69757595808191081378569923259284847281/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (380985682)
      previous := (190492841)
      next := (190492841)
      square := (1324624862050169073555763721203700000000000000)
      linear := (-95507530996689403551114490648768070000000000000)
      constant := (1716782002932506546268271181582691008022720425952) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 69 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 69 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel069

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (411907586687560729107/100000000000000000000)
  centralHi := (102976896671890182277/25000000000000000000)
  directionLo := (103731316257005953893/25000000000000000000)
  directionHi := (414925265028023815573/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree070.table
  base := (-1781199812529930939402756535709252205681/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-1975205595554415528032525875399530000000000000)
      constant := (36002283056897946586854010062170784154403648239) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree070.table
  base := (-222651547284265499151562749867469974671/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3931290000000000000000000000000000000000000000
      center := (69976962)
      previous := (34988481)
      next := (34988481)
      square := (243298444050031054326568846751700000000000000)
      linear := (-17796252149786392946417658623950770000000000000)
      constant := (324729735205890537170976035393347961170620515528) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 70 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 70 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel070

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103731316257005953893/25000000000000000000)
  centralHi := (414925265028023815573/100000000000000000000)
  directionLo := (417921154222158572021/100000000000000000000)
  directionHi := (208960577111079286011/50000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree071.table
  base := (-10481017008479261451676293644486000083/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-2003402863392218170160751291982130000000000000)
      constant := (37060344006899335235231757061075330878796809625) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree071.table
  base := (-1310137876114271148581744665179061737261/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (3428871138)
      previous := (1714435569)
      next := (1714435569)
      square := (11921623758451521662001873490833300000000000000)
      linear := (-884464931708861876788900129308262830000000000000)
      constant := (16379361544733871779752005263032738641276323696219) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 71 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 71 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel071

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (417921154222158572021/100000000000000000000)
  centralHi := (208960577111079286011/50000000000000000000)
  directionLo := (10522392988710632881/2500000000000000000)
  directionHi := (420895719548425315241/100000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree072.table
  base := (-819014371637271528131369396257577636429/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-2031600131230020812288976708564730000000000000)
      constant := (38133986079234897316736720986259432751263144851) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree072.table
  base := (-819023566535933062316804941386682564377/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (380985682)
      previous := (190492841)
      next := (190492841)
      square := (1324624862050169073555763721203700000000000000)
      linear := (-99657056453132277689259442893659770000000000000)
      constant := (1872650167570798166033804651860667167626366964887) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 72 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 72 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel072

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10522392988710632881/2500000000000000000)
  centralHi := (420895719548425315241/100000000000000000000)
  directionLo := (423849409958291840579/100000000000000000000)
  directionHi := (21192470497914592029/5000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree073.table
  base := (-15393248285645199227149002172444430051/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-2059797399067823454417202125147330000000000000)
      constant := (39223209124670641876343548705968499097018845380) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree073.table
  base := (-307872828915243999329280396060983460447/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (3428871138)
      previous := (1714435569)
      next := (1714435569)
      square := (11921623758451521662001873490833300000000000000)
      linear := (-909362084447519121617769842777613030000000000000)
      constant := (17335226850200564210950444404829044280025718635513) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 73 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 73 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel073

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (423849409958291840579/100000000000000000000)
  centralHi := (21192470497914592029/5000000000000000000)
  directionLo := (426782658867247778549/100000000000000000000)
  directionHi := (8535653177344955571/2000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree074.table
  base := (223318209927271791897354526483003564501/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-2087994666905626096545427541729930000000000000)
      constant := (40328013017327278004613489280149324078700968181) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree074.table
  base := (223311486813621047318619572653857211433/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (3428871138)
      previous := (1714435569)
      next := (1714435569)
      square := (11921623758451521662001873490833300000000000000)
      linear := (-921810660816847744032204699512288130000000000000)
      constant := (17823487516024817087929082764676189843351998748993) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 74 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 74 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel074

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (426782658867247778549/100000000000000000000)
  centralHi := (8535653177344955571/2000000000000000000)
  directionLo := (429695884897217784983/100000000000000000000)
  directionHi := (53711985612152223123/12500000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree075.table
  base := (154906544900593101980447110057802969403/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-2116191934743428738673652958312530000000000000)
      constant := (41448397651025891841332817843424424457532462215) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree075.table
  base := (774526977225823941161181040448432472659/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (380985682)
      previous := (190492841)
      next := (190492841)
      square := (1324624862050169073555763721203700000000000000)
      linear := (-103806581909575151827404395138551470000000000000)
      constant := (2035403717701333107649375121496588820963072671171) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 75 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 75 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel075

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (429695884897217784983/100000000000000000000)
  centralHi := (53711985612152223123/12500000000000000000)
  directionLo := (108147373143493550641/25000000000000000000)
  directionHi := (86517898514794840513/20000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree076.table
  base := (84111032979364505065708579042240465507/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (21538)
      previous := (10769)
      next := (10769)
      square := (74884100969538643990941473300000000000000)
      linear := (-5940136295238868090863929016330000000000000)
      constant := (117962224200014936422975751097305777541221552) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree076.table
  base := (336442903865837959559927983636897117311/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 533610000000000000000000000000000000000000000
      center := (9498258)
      previous := (4749129)
      next := (4749129)
      square := (33023888527566542000005189725300000000000000)
      linear := (-2622459317328268667205192279727530000000000000)
      constant := (52134805099773103409587327410167173868307329084) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 76 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 76 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel076

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (108147373143493550641/25000000000000000000)
  centralHi := (86517898514794840513/20000000000000000000)
  directionLo := (54432984122854844891/12500000000000000000)
  directionHi := (435463872982838759129/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree077.table
  base := (193704788999140014353451788789507182673/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (64258)
      previous := (32129)
      next := (32129)
      square := (223414549173582235377932825300000000000000)
      linear := (-17955260086107719197769452822130000000000000)
      constant := (361453791713407141497045829628840120929449530) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree077.table
  base := (242130461530993365318577284396761122837/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32490000000000000000000000000000000000000000
      center := (578322)
      previous := (289161)
      next := (289161)
      square := (2010730942562240118401395427700000000000000)
      linear := (-161773720682211774544697127629670000000000000)
      constant := (3260175582428186610785723625375480615104779304) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 77 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 77 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel077

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54432984122854844891/12500000000000000000)
  centralHi := (435463872982838759129/100000000000000000000)
  directionLo := (219159702192841199453/50000000000000000000)
  directionHi := (438319404385682398907/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree078.table
  base := (2548345352725029393165497996152949993127/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-2200783738256836665058329208060330000000000000)
      constant := (44903035170657170787550554688800497008649780487) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree078.table
  base := (637085441533375194505687131219736345007/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (380985682)
      previous := (190492841)
      next := (190492841)
      square := (1324624862050169073555763721203700000000000000)
      linear := (-107956107366018025965549347383443170000000000000)
      constant := (2205042510348982570187500229092488933444105150332) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 78 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 78 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel078

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (219159702192841199453/50000000000000000000)
  centralHi := (438319404385682398907/100000000000000000000)
  directionLo := (110289113200494777183/25000000000000000000)
  directionHi := (441156452801979108733/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree079.table
  base := (3179667685464608463421866872202534518977/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-2228981006094639307186554624642930000000000000)
      constant := (46085742002464742697317208634719848910323434337) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree079.table
  base := (3179664621550712485597567199949036131379/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (3428871138)
      previous := (1714435569)
      next := (1714435569)
      square := (11921623758451521662001873490833300000000000000)
      linear := (-984053542663490856104378983185663630000000000000)
      constant := (20368069312374562838528330089275221136639351849659) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 79 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 79 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel079

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (110289113200494777183/25000000000000000000)
  centralHi := (441156452801979108733/100000000000000000000)
  directionLo := (443975372556440643209/100000000000000000000)
  directionHi := (44397537255644064321/10000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree080.table
  base := (3831013850410713216296805047633043890507/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-2257178273932441949314780041225530000000000000)
      constant := (47284029247412863204670231341648058990181236267) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree080.table
  base := (3831011233423486699928856898276265167129/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (3428871138)
      previous := (1714435569)
      next := (1714435569)
      square := (11921623758451521662001873490833300000000000000)
      linear := (-996502119032819478518813839920338730000000000000)
      constant := (20897641166171507661807067941869092442595524575409) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 80 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 80 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel080

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (443975372556440643209/100000000000000000000)
  centralHi := (44397537255644064321/10000000000000000000)
  directionLo := (22338825339777588329/5000000000000000000)
  directionHi := (446776506795551766581/100000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree081.table
  base := (2251191486115639631995723323454829244553/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-2285375541770244591443005457808130000000000000)
      constant := (48497896867266152405086180549275890792462639186) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree081.table
  base := (900476147465544093855016524132514465273/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (380985682)
      previous := (190492841)
      next := (190492841)
      square := (1324624862050169073555763721203700000000000000)
      linear := (-112105632822460900103694299628334870000000000000)
      constant := (2381566459764444291803030102432414149267609528685) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 81 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 81 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel081

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22338825339777588329/5000000000000000000)
  centralHi := (446776506795551766581/100000000000000000000)
  directionLo := (89912037595027543739/20000000000000000000)
  directionHi := (56195023496892214837/12500000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree082.table
  base := (5193774312638083909553913115668153194077/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-2313572809608047233571230874390730000000000000)
      constant := (49727344829775442442939501250470160599670477437) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree082.table
  base := (2596886202162178266006026518239761783031/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (3428871138)
      previous := (1714435569)
      next := (1714435569)
      square := (11921623758451521662001873490833300000000000000)
      linear := (-1021399271771476723347683553389688930000000000000)
      constant := (21977440213458248682320891250375813182380117011902) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 82 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 82 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel082

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (89912037595027543739/20000000000000000000)
  centralHi := (56195023496892214837/12500000000000000000)
  directionLo := (9046534766418501013/2000000000000000000)
  directionHi := (452326738320925050651/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree083.table
  base := (5905187248941189753548957585315200166909/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-2341770077445849875699456290973330000000000000)
      constant := (50972373107741014162685462426763843258490752029) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree083.table
  base := (738148202466819541466637173653010274217/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (3428871138)
      previous := (1714435569)
      next := (1714435569)
      square := (11921623758451521662001873490833300000000000000)
      linear := (-1033847848140805345762118410124364030000000000000)
      constant := (22527667381065502051068690621997519126228320757256) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 83 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 83 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel083

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9046534766418501013/2000000000000000000)
  centralHi := (452326738320925050651/100000000000000000000)
  directionLo := (113769117565975492279/25000000000000000000)
  directionHi := (455076470263901969117/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree084.table
  base := (1659155313989736647208260627868884179663/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-2369967345283652517827681707555930000000000000)
      constant := (52232981678222407901625827214681082919407438012) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree084.table
  base := (6636619865239523508069891881165015195817/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-2372554250589872943711005140269930000000000000)
      constant := (52346439071921127840923497363286189028768482377) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 84 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 84 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel084

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (113769117565975492279/25000000000000000000)
  centralHi := (455076470263901969117/100000000000000000000)
  directionLo := (457809686852143288673/100000000000000000000)
  directionHi := (228904843426071644337/50000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree085.table
  base := (3694037945379265061251136626008290579703/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-2398164613121455159955907124138530000000000000)
      constant := (53509170521871874961822260592358886281624013486) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree085.table
  base := (1847018675946056015821946442269801494039/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (3428871138)
      previous := (1714435569)
      next := (1714435569)
      square := (11921623758451521662001873490833300000000000000)
      linear := (-1058745000879462590590988123593714230000000000000)
      constant := (23648776953994263248092330545921288419143811374076) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 85 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 85 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel085

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (457809686852143288673/100000000000000000000)
  centralHi := (228904843426071644337/50000000000000000000)
  directionLo := (9210533642812732183/2000000000000000000)
  directionHi := (460526682140636609151/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree086.table
  base := (203988769494603539343910125617138183429/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-2426361880959257802084132540721130000000000000)
      constant := (54800939622372124496730627067463668519614485960) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree086.table
  base := (8159549766845816189187002222170425942489/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (3428871138)
      previous := (1714435569)
      next := (1714435569)
      square := (11921623758451521662001873490833300000000000000)
      linear := (-1071193577248791213005422980328389330000000000000)
      constant := (24219659343797665864220322514913765861636893145969) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 86 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 86 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel086

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9210533642812732183/2000000000000000000)
  centralHi := (460526682140636609151/100000000000000000000)
  directionLo := (18529109662421166313/4000000000000000000)
  directionHi := (231613870780264578913/50000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree087.table
  base := (895104560799928518638875641226650593017/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-2454559148797060444212357957303730000000000000)
      constant := (56108288965962047335224062589010023245535755770) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree087.table
  base := (1790208948739278722403079048783424601481/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (380985682)
      previous := (190492841)
      next := (190492841)
      square := (1324624862050169073555763721203700000000000000)
      linear := (-120404683735346648379984204118118270000000000000)
      constant := (2755269643793530424891337420157420238654236432445) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 87 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 87 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel087

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18529109662421166313/4000000000000000000)
  centralHi := (231613870780264578913/50000000000000000000)
  directionLo := (1455978569590961719/312500000000000000)
  directionHi := (465913142269107750081/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree088.table
  base := (1952512021945598414009659092289711995417/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (64258)
      previous := (32129)
      next := (32129)
      square := (223414549173582235377932825300000000000000)
      linear := (-20518648071362504845789945238730000000000000)
      constant := (474638169760633483307463997770622930151727685) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree088.table
  base := (9762559372347662377246828537488941834991/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1592010000000000000000000000000000000000000000
      center := (28337778)
      previous := (14168889)
      next := (14168889)
      square := (98525816185549765801668375957300000000000000)
      linear := (-9058601074276433535820600775187930000000000000)
      constant := (209769250413056384486025429578964817029072402191) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 88 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 88 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel088

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1455978569590961719/312500000000000000)
  centralHi := (465913142269107750081/100000000000000000000)
  directionLo := (234291576740863266811/50000000000000000000)
  directionHi := (468583153481726533623/100000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree089.table
  base := (2118818812185832964951054120327909426773/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-2510953684472665728468808790468930000000000000)
      constant := (58769728337809597756139354962814687058354357065) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree089.table
  base := (10594093431914099919529501649003961897079/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (3428871138)
      previous := (1714435569)
      next := (1714435569)
      square := (11921623758451521662001873490833300000000000000)
      linear := (-1108539306356777080248727550532414630000000000000)
      constant := (25973616857056823235152327897756574868295201739359) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 89 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 89 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel089

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (234291576740863266811/50000000000000000000)
  centralHi := (468583153481726533623/100000000000000000000)
  directionLo := (235619018393403852407/50000000000000000000)
  directionHi := (94247607357361540963/20000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree090.table
  base := (2861411818169952247071790232456337567929/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-2539150952310468370597034207051530000000000000)
      constant := (60123818348028540841928354351153401125218826596) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree090.table
  base := (5722823368086205186777004010863493434301/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (380985682)
      previous := (190492841)
      next := (190492841)
      square := (1324624862050169073555763721203700000000000000)
      linear := (-124554209191789522518129156363009970000000000000)
      constant := (2952448829087277426124484630522264819156962794138) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 90 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 90 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel090

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (235619018393403852407/50000000000000000000)
  centralHi := (94247607357361540963/20000000000000000000)
  directionLo := (118469511611239607283/25000000000000000000)
  directionHi := (473878046444958429133/100000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree091.table
  base := (12317219585678001480674805947847548764627/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-2567348220148271012725259623634130000000000000)
      constant := (61493488564735013435514008995541458777587671987) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree091.table
  base := (12317219128129891769901034356823339600559/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3931290000000000000000000000000000000000000000
      center := (69976962)
      previous := (34988481)
      next := (34988481)
      square := (243298444050031054326568846751700000000000000)
      linear := (-23131356308070088266889740081668670000000000000)
      constant := (554639736962074336939161671310431572673828159111) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 91 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 91 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel091

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (118469511611239607283/25000000000000000000)
  centralHi := (473878046444958429133/100000000000000000000)
  directionLo := (476503429673172052939/100000000000000000000)
  directionHi := (23825171483658602647/5000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree092.table
  base := (13208810865606041061071172559021391849859/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-2595545487986073654853485040216730000000000000)
      constant := (62878738982061884028994879643282573417393690979) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree092.table
  base := (13208810475443681398863836875719092875589/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (3428871138)
      previous := (1714435569)
      next := (1714435569)
      square := (11921623758451521662001873490833300000000000000)
      linear := (-1145885035464762947492032120736439930000000000000)
      constant := (27789539802575897213411997735017443451891283971069) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 92 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 92 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel092

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (476503429673172052939/100000000000000000000)
  centralHi := (23825171483658602647/5000000000000000000)
  directionLo := (119778606728753181527/25000000000000000000)
  directionHi := (479114426915012726109/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree093.table
  base := (14120420999219190215875908525880109150677/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-2623742755823876296981710456799330000000000000)
      constant := (64279569595062509243039389308291959047810722037) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree093.table
  base := (14120420666557599018834689820906180243473/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (380985682)
      previous := (190492841)
      next := (190492841)
      square := (1324624862050169073555763721203700000000000000)
      linear := (-128703734648232396656274108607901670000000000000)
      constant := (3156513059326590937307960224419158500101542061537) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 93 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 93 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel093

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119778606728753181527/25000000000000000000)
  centralHi := (479114426915012726109/100000000000000000000)
  directionLo := (481711272097619195171/100000000000000000000)
  directionHi := (120427818024404798793/25000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree094.table
  base := (1505204989104647634284488175826796533267/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-2651940023661678939109935873381930000000000000)
      constant := (65695980399566621523408912056739522993696358270) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree094.table
  base := (7526024803722091903058464475195331326079/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (3428871138)
      previous := (1714435569)
      next := (1714435569)
      square := (11921623758451521662001873490833300000000000000)
      linear := (-1170782188203420192320901834205790130000000000000)
      constant := (29034580303420625016436061498553345280071230896718) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 94 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 94 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel094

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (481711272097619195171/100000000000000000000)
  centralHi := (120427818024404798793/25000000000000000000)
  directionLo := (96858838575261052691/20000000000000000000)
  directionHi := (15134193527384539483/3125000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree095.table
  base := (500115545643993240986330995880101376421/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (21538)
      previous := (10769)
      next := (10769)
      square := (74884100969538643990941473300000000000000)
      linear := (-7424203023544270308138950941730000000000000)
      constant := (185950059257780523365327336332897752529502112) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree095.table
  base := (16003697218857127276507235864151373447927/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 533610000000000000000000000000000000000000000
      center := (9498258)
      previous := (4749129)
      next := (4749129)
      square := (33023888527566542000005189725300000000000000)
      linear := (-3277647547292933004807026844710430000000000000)
      constant := (82181241300535373620523612797106331438554832647) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 95 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 95 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel095

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96858838575261052691/20000000000000000000)
  centralHi := (15134193527384539483/3125000000000000000)
  directionLo := (243431705433740394179/50000000000000000000)
  directionHi := (486863410867480788359/100000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree096.table
  base := (16975363640066451976667462106633443353053/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-2708334559337284223366386706547130000000000000)
      constant := (68575542569575778316916419352631535439104708093) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree096.table
  base := (16975363434014153022393978236135969635867/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (380985682)
      previous := (190492841)
      next := (190492841)
      square := (1324624862050169073555763721203700000000000000)
      linear := (-132853260104675270794419060852793370000000000000)
      constant := (3367462327874533843326664496283091629193551014923) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 96 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 96 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel096

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (243431705433740394179/50000000000000000000)
  centralHi := (486863410867480788359/100000000000000000000)
  directionLo := (244709570935283841339/50000000000000000000)
  directionHi := (489419141870567682679/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree097.table
  base := (17967048372249236850356759994746614597823/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-2736531827175086865494612123129730000000000000)
      constant := (70038693929620265185773153708693636872247506463) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree097.table
  base := (17967048196642916948000563243542388651457/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (3428871138)
      previous := (1714435569)
      next := (1714435569)
      square := (11921623758451521662001873490833300000000000000)
      linear := (-1208127917311406059564206404409815430000000000000)
      constant := (30953778826469236927489530987098730069699773308697) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 97 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 97 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel097

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244709570935283841339/50000000000000000000)
  centralHi := (489419141870567682679/100000000000000000000)
  directionLo := (245980798039769916843/50000000000000000000)
  directionHi := (491961596079539833687/100000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree098.table
  base := (18978751608976150721467817972211100069069/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-2764729095012889507622837539712330000000000000)
      constant := (71517425470087679502610175002661293062117002989) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree098.table
  base := (18978751459333063039281001428899604336483/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3931290000000000000000000000000000000000000000
      center := (69976962)
      previous := (34988481)
      next := (34988481)
      square := (243298444050031054326568846751700000000000000)
      linear := (-24909724360831320040380433900907970000000000000)
      constant := (645046566028067060878261783218902482553197225307) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 98 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 98 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel098

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (245980798039769916843/50000000000000000000)
  centralHi := (491961596079539833687/100000000000000000000)
  directionLo := (494490978284673814009/100000000000000000000)
  directionHi := (49449097828467381401/10000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree099.table
  base := (20010473309651694964188283522197423746873/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (64258)
      previous := (32129)
      next := (32129)
      square := (223414549173582235377932825300000000000000)
      linear := (-23082036056617290493810437655330000000000000)
      constant := (603402786687642721421102263340883269972621153) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree099.table
  base := (10005236591073238402163173617089913609983/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 176890000000000000000000000000000000000000000
      center := (3148642)
      previous := (1574321)
      next := (1574321)
      square := (10947312909505529533518708439700000000000000)
      linear := (-1132254426124943346550115810724670000000000000)
      constant := (29630550667419293881527525911271336963693978574) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 99 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 99 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel099

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (494490978284673814009/100000000000000000000)
  centralHi := (49449097828467381401/10000000000000000000)
  directionLo := (248503744032529214077/50000000000000000000)
  directionHi := (99401497613011685631/20000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree100.table
  base := (21062213440076582421956385699928713188277/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-2821123630688494791879288372877530000000000000)
      constant := (74521629085477675491516975576811586120777127637) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree100.table
  base := (21062213331445290473607862706612022673207/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (3428871138)
      previous := (1714435569)
      next := (1714435569)
      square := (11921623758451521662001873490833300000000000000)
      linear := (-1245473646419391926807510974613840730000000000000)
      constant := (32934942650154235044735489908134411715213264540447) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 100 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 100 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel100

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (248503744032529214077/50000000000000000000)
  centralHi := (99401497613011685631/20000000000000000000)
  directionLo := (99902263994475048599/20000000000000000000)
  directionHi := (124877829993093810749/25000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree101.table
  base := (11066985985722724127589884461729424757083/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-2849320898526297434007513789460130000000000000)
      constant := (76047101157648150959742746456180436005628285046) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree101.table
  base := (5533492969725882345283224166555973347117/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (3428871138)
      previous := (1714435569)
      next := (1714435569)
      square := (11921623758451521662001873490833300000000000000)
      linear := (-1257922222788720549221945831348515830000000000000)
      constant := (33609100654833505663661985726685163796211836782228) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 101 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 101 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel101

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99902263994475048599/20000000000000000000)
  centralHi := (124877829993093810749/25000000000000000000)
  directionLo := (62750332963303630081/12500000000000000000)
  directionHi := (502002663706429040649/100000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree102.table
  base := (23225748879501445730380629738671535786079/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-2877518166364100076135739206042730000000000000)
      constant := (77588153404656632374465642569674171354671716799) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree102.table
  base := (2322574880067363195409410660624794235969/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (380985682)
      previous := (190492841)
      next := (190492841)
      square := (1324624862050169073555763721203700000000000000)
      linear := (-141152311017561019070708965342576770000000000000)
      constant := (3810015965599782184457634495906881692140467325610) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 102 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 102 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel102

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (62750332963303630081/12500000000000000000)
  centralHi := (502002663706429040649/100000000000000000000)
  directionLo := (504481704282876382663/100000000000000000000)
  directionHi := (63060213035359547833/12500000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree103.table
  base := (6084386035955794317491686817807992838457/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-2905715434201902718263964622625330000000000000)
      constant := (79144785825611092668098858117280973740706560868) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree103.table
  base := (12168772038341790924870120752003857159569/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (3428871138)
      previous := (1714435569)
      next := (1714435569)
      square := (11921623758451521662001873490833300000000000000)
      linear := (-1282819375527377794050815544817866030000000000000)
      constant := (34978071756461183340178000745963331177405851737298) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 103 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 103 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel103

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (504481704282876382663/100000000000000000000)
  centralHi := (63060213035359547833/12500000000000000000)
  directionLo := (101389724438714396103/20000000000000000000)
  directionHi := (126737155548392995129/25000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree104.table
  base := (25469357747223252330599007284930072984563/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-2933912702039705360392190039207930000000000000)
      constant := (80716998419760769434318797250048950518038696403) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree104.table
  base := (25469357690044191078691334409614727341457/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (3428871138)
      previous := (1714435569)
      next := (1714435569)
      square := (11921623758451521662001873490833300000000000000)
      linear := (-1295267951896706416465250401552541130000000000000)
      constant := (35672884852697594854171085680764258899105962798697) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 104 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 104 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel104

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (101389724438714396103/20000000000000000000)
  centralHi := (126737155548392995129/25000000000000000000)
  directionLo := (509403593559926143579/100000000000000000000)
  directionHi := (25470179677996307179/5000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree105.table
  base := (3327648709405125488959644745391411823561/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-2962109969877508002520415455790530000000000000)
      constant := (82304791186474006277872240368375688078919744328) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree105.table
  base := (6655297406637319499122718298550036245627/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-2965343601510283534874569746683030000000000000)
      constant := (82482047571051283367112225859151756532980931948) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 105 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 105 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel105

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (509403593559926143579/100000000000000000000)
  centralHi := (25470179677996307179/5000000000000000000)
  directionLo := (127961697569910513253/25000000000000000000)
  directionHi := (511846790279642053013/100000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree106.table
  base := (6948259978928657187388032852598357591451/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-2990307237715310644648640872373130000000000000)
      constant := (83908164125219563470399732537520375431808684524) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree106.table
  base := (13896519937127093533263919733403914298367/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (3428871138)
      previous := (1714435569)
      next := (1714435569)
      square := (11921623758451521662001873490833300000000000000)
      linear := (-1320165104635363661294120115021891330000000000000)
      constant := (37083166134639152938518053215926436777571866593614) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 106 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 106 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel106

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (127961697569910513253/25000000000000000000)
  centralHi := (511846790279642053013/100000000000000000000)
  directionLo := (128569595041794708743/25000000000000000000)
  directionHi := (514278380167178834973/100000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree107.table
  base := (14492454229210160925278926062879143850491/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-3018504505553113286776866288955730000000000000)
      constant := (85527117235550854985972945913525657765066594742) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree107.table
  base := (14492454211560188465231331751560917611077/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (3428871138)
      previous := (1714435569)
      next := (1714435569)
      square := (11921623758451521662001873490833300000000000000)
      linear := (-1332613681004692283708554971756566430000000000000)
      constant := (37798634319920830130478299358284415823993458813434) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 107 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 107 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel107

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (128569595041794708743/25000000000000000000)
  centralHi := (514278380167178834973/100000000000000000000)
  directionLo := (516698527088265239319/100000000000000000000)
  directionHi := (12917463177206630983/2500000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree108.table
  base := (6039359058953584173757937455817045531853/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-3046701773390915928905091705538330000000000000)
      constant := (87161650517092653943160420229738161829384354465) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree108.table
  base := (15098397632357862941723906942408055284261/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (380985682)
      previous := (190492841)
      next := (190492841)
      square := (1324624862050169073555763721203700000000000000)
      linear := (-149451361930446767346998869832360170000000000000)
      constant := (4280109726057357430407298308576784633761436864618) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 108 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 108 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel108

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (516698527088265239319/100000000000000000000)
  centralHi := (12917463177206630983/2500000000000000000)
  directionLo := (519107391088769043077/100000000000000000000)
  directionHi := (259553695544384521539/50000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree109.table
  base := (7857175104386054096398694394030242619627/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-3074899041228718571033317122120930000000000000)
      constant := (88811763969529880141345979939325610111471707948) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree109.table
  base := (7857175097990456317493838074280136948581/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (3428871138)
      previous := (1714435569)
      next := (1714435569)
      square := (11921623758451521662001873490833300000000000000)
      linear := (-1357510833743349528537424685225916630000000000000)
      constant := (39250225778288959509979981638840758807857905190004) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 109 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 109 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel109

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (519107391088769043077/100000000000000000000)
  centralHi := (259553695544384521539/50000000000000000000)
  directionLo := (104301025703641795037/20000000000000000000)
  directionHi := (260752564259104487593/50000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree110.table
  base := (2042538988793529250546008870617667154603/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (64258)
      previous := (32129)
      next := (32129)
      square := (223414549173582235377932825300000000000000)
      linear := (-25645424041872076141830930071930000000000000)
      constant := (747747583409902015102944805548987645484986928) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree110.table
  base := (32680623798920898761044098177391366809559/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1592010000000000000000000000000000000000000000
      center := (28337778)
      previous := (14168889)
      next := (14168889)
      square := (98525816185549765801668375957300000000000000)
      linear := (-11321978595972546702081483817856130000000000000)
      constant := (330465694637394022710491228038647432987448602359) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 110 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 110 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel110

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (104301025703641795037/20000000000000000000)
  centralHi := (260752564259104487593/50000000000000000000)
  directionLo := (261945946074089447131/50000000000000000000)
  directionHi := (523891892148178894263/100000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree111.table
  base := (33952565499149833542519390384014067271299/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-3131293576904323855289767955286130000000000000)
      constant := (92158731386075770819541318178360248472477611619) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree111.table
  base := (339525654806161387252917265914150545743/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (380985682)
      previous := (190492841)
      next := (190492841)
      square := (1324624862050169073555763721203700000000000000)
      linear := (-153600887386889641485143822077251870000000000000)
      constant := (4525484150325277638297319278464860518944139916700) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 111 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 111 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel111

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (261945946074089447131/50000000000000000000)
  centralHi := (523891892148178894263/100000000000000000000)
  directionLo := (8222934863842781989/1562500000000000000)
  directionHi := (526267831285938047297/100000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree112.table
  base := (35244525448653403164350148372280274303277/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-3159490844742126497417993371868730000000000000)
      constant := (93855585349777077125640225184696134661841442637) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree112.table
  base := (35244525432880223515612689855631193502737/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3931290000000000000000000000000000000000000000
      center := (69976962)
      previous := (34988481)
      next := (34988481)
      square := (243298444050031054326568846751700000000000000)
      linear := (-28466460466353783587361821539386570000000000000)
      constant := (846515320073819368275527418233749875470537494073) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 112 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 112 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel112

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8222934863842781989/1562500000000000000)
  centralHi := (526267831285938047297/100000000000000000000)
  directionLo := (264316545941703202811/50000000000000000000)
  directionHi := (528633091883406405623/100000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree113.table
  base := (9139125916412590289017037951786135750053/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-3187688112579929139546218788451330000000000000)
      constant := (95568019483546697478368083994827470782792260372) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree113.table
  base := (7311300730445519950685929453711955594811/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (3428871138)
      previous := (1714435569)
      next := (1714435569)
      square := (11921623758451521662001873490833300000000000000)
      linear := (-1407305139220664018195164112164617030000000000000)
      constant := (42236029043126484316850178717227362550802951136655) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 113 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 113 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel113

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264316545941703202811/50000000000000000000)
  centralHi := (528633091883406405623/100000000000000000000)
  directionLo := (132746954160447558513/25000000000000000000)
  directionHi := (530987816641790234053/100000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree114.table
  base := (9472125036792124596624324585963872409761/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (21538)
      previous := (10769)
      next := (10769)
      square := (74884100969538643990941473300000000000000)
      linear := (-8908269751849672525413972867130000000000000)
      constant := (269518099133669813879961194687626514246324324) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree114.table
  base := (37888500135746805468165474454581133860631/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 59290000000000000000000000000000000000000000
      center := (1055362)
      previous := (527681)
      next := (527681)
      square := (3669320947507393555556132191700000000000000)
      linear := (-436981753028621926934317934410370000000000000)
      constant := (13234746824068765814775426123545741542659681199) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 114 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 114 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel114

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132746954160447558513/25000000000000000000)
  centralHi := (530987816641790234053/100000000000000000000)
  directionLo := (1333330362780125313/250000000000000000)
  directionHi := (533332145112050125201/100000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree115.table
  base := (19620257445363944879867019007330215522319/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-3244082648255534423802669621616530000000000000)
      constant := (99039628260793067514419784080771832288460832478) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree115.table
  base := (2452532180063105835301394606442485157003/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (3428871138)
      previous := (1714435569)
      next := (1714435569)
      square := (11921623758451521662001873490833300000000000000)
      linear := (-1432202291959321263024033825633967230000000000000)
      constant := (43770240848389182310787560340580087603873346991408) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 115 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 115 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel115

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1333330362780125313/250000000000000000)
  centralHi := (533332145112050125201/100000000000000000000)
  directionLo := (267833106895705827843/50000000000000000000)
  directionHi := (535666213791411655687/100000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree116.table
  base := (10153136973565762346232607611555511232439/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-3272279916093337065930895038199130000000000000)
      constant := (100798802904071269100431333506995705144576671836) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree116.table
  base := (5076568485749363190111368872725475371399/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (3428871138)
      previous := (1714435569)
      next := (1714435569)
      square := (11921623758451521662001873490833300000000000000)
      linear := (-1444650868328649885438468682368642330000000000000)
      constant := (44547674294056832786079593197406310595654825248632) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 116 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 116 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel116

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (267833106895705827843/50000000000000000000)
  centralHi := (535666213791411655687/100000000000000000000)
  directionLo := (537990156216107531393/100000000000000000000)
  directionHi := (268995078108053765697/50000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree117.table
  base := (42004599156057296757058382276373440219501/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-3300477183931139708059120454781730000000000000)
      constant := (102573557717014421247560507414751978242228023181) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree117.table
  base := (42004599149023365769540723548443232826747/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (380985682)
      previous := (190492841)
      next := (190492841)
      square := (1324624862050169073555763721203700000000000000)
      linear := (-161899938299775389761433726567035270000000000000)
      constant := (5036888085374447441655149937425658333802151649643) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 117 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 117 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel117

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (537990156216107531393/100000000000000000000)
  centralHi := (268995078108053765697/50000000000000000000)
  directionLo := (21612164122021181117/4000000000000000000)
  directionHi := (270152051525264763963/50000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree118.table
  base := (21708334337343710984904888388840984958847/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-3328674451768942350187345871364330000000000000)
      constant := (104363892699560356723889860957269666127974791614) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree118.table
  base := (21708334334351952990757210868091645247523/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (3428871138)
      previous := (1714435569)
      next := (1714435569)
      square := (11921623758451521662001873490833300000000000000)
      linear := (-1469548021067307130267338395837992530000000000000)
      constant := (46123196271301966358998977937477775029642320007766) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 118 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 118 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel118

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21612164122021181117/4000000000000000000)
  centralHi := (270152051525264763963/50000000000000000000)
  directionLo := (108521636434591729381/20000000000000000000)
  directionHi := (271304091086479323453/50000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree119.table
  base := (44848756448977037207144072759849226670133/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-3356871719606744992315571287946930000000000000)
      constant := (106169807851657689733226927254815344070178079573) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree119.table
  base := (2242437822194371879739138794130546974129/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3931290000000000000000000000000000000000000000
      center := (69976962)
      previous := (34988481)
      next := (34988481)
      square := (243298444050031054326568846751700000000000000)
      linear := (-30244828519115015360852515358625870000000000000)
      constant := (957577240874092156664483274825392586027847192820) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 119 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 119 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel119

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (108521636434591729381/20000000000000000000)
  centralHi := (271304091086479323453/50000000000000000000)
  directionLo := (272451259379016325171/50000000000000000000)
  directionHi := (544902518758032650343/100000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree120.table
  base := (46300862477957254163892186999490883116263/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-3385068987444547634443796704529530000000000000)
      constant := (107991303173264098265513615583108361265401484103) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree120.table
  base := (9260172494725665729091733975274506521191/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (380985682)
      previous := (190492841)
      next := (190492841)
      square := (1324624862050169073555763721203700000000000000)
      linear := (-166049463756218263899578678811926970000000000000)
      constant := (5302917595881939879501137677590337001241275297395) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 120 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 120 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel120

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (272451259379016325171/50000000000000000000)
  centralHi := (544902518758032650343/100000000000000000000)
  directionLo := (547187235356101459189/100000000000000000000)
  directionHi := (54718723535610145919/10000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree121.table
  base := (47772986760833539954259082820758446421259/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (64258)
      previous := (32129)
      next := (32129)
      square := (223414549173582235377932825300000000000000)
      linear := (-28208812027126861789851422488530000000000000)
      constant := (907672550944998977931946387976123799158074499) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree121.table
  base := (5971623344643982058428966513469822230713/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1592010000000000000000000000000000000000000000
      center := (28337778)
      previous := (14168889)
      next := (14168889)
      square := (98525816185549765801668375957300000000000000)
      linear := (-12453667356820603285211925339190230000000000000)
      constant := (401141462409982416069813172920140853351613922504) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 121 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 121 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel121

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (547187235356101459189/100000000000000000000)
  centralHi := (54718723535610145919/10000000000000000000)
  directionLo := (274731225984806383647/50000000000000000000)
  directionHi := (109892490393922553459/20000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree122.table
  base := (24632564648478891829892967451631921361033/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-3441463523120152918700247537694730000000000000)
      constant := (111681034324871713792953419392003327913942564946) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree122.table
  base := (49265129293826783259062841882718970400089/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (3428871138)
      previous := (1714435569)
      next := (1714435569)
      square := (11921623758451521662001873490833300000000000000)
      linear := (-1519342326544621619925077822776692930000000000000)
      constant := (49356860568829596226970836233429037489606412835569) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 122 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 122 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel122

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (274731225984806383647/50000000000000000000)
  centralHi := (109892490393922553459/20000000000000000000)
  directionLo := (551728286126662590237/100000000000000000000)
  directionHi := (275864143063331295119/50000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree123.table
  base := (50777290085804757158180563807674881900203/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-3469660790957955560828472954277330000000000000)
      constant := (113549270154821668165467490233695936516282767243) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree123.table
  base := (3173580630196390688365636584839642880093/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (380985682)
      previous := (190492841)
      next := (190492841)
      square := (1324624862050169073555763721203700000000000000)
      linear := (-170198989212661138037723631056818670000000000000)
      constant := (5575832134954754415701766833492586475465948389072) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 123 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 123 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel123

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (551728286126662590237/100000000000000000000)
  centralHi := (275864143063331295119/50000000000000000000)
  directionLo := (5539848529518383051/1000000000000000000)
  directionHi := (553984852951838305101/100000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree124.table
  base := (52309469126952281658625884310275591433703/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-3497858058795758202956698370859930000000000000)
      constant := (115433086154176298255546044370531668109415580743) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree124.table
  base := (5230946912468831822222909160437403160789/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (3428871138)
      previous := (1714435569)
      next := (1714435569)
      square := (11921623758451521662001873490833300000000000000)
      linear := (-1544239479283278864753947536246043130000000000000)
      constant := (51015002888889556052592620901013377994926931202690) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 124 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 124 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel124

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5539848529518383051/1000000000000000000)
  centralHi := (553984852951838305101/100000000000000000000)
  directionLo := (69529033154309376209/12500000000000000000)
  directionHi := (556232265234475009673/100000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree125.table
  base := (53861666420064519156947006980282195462859/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-3526055326633560845084923787442530000000000000)
      constant := (117332482322920934323328718457284456580013143979) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree125.table
  base := (53861666418139566937162337967107122000823/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (3428871138)
      previous := (1714435569)
      next := (1714435569)
      square := (11921623758451521662001873490833300000000000000)
      linear := (-1556688055652607487168382392980718230000000000000)
      constant := (51854401591713626530428055413190031932488015713183) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 125 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 125 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel125

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69529033154309376209/12500000000000000000)
  centralHi := (556232265234475009673/100000000000000000000)
  directionLo := (22338825339777588329/4000000000000000000)
  directionHi := (279235316747219854113/50000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree126.table
  base := (55433881964877898944214626899781686852173/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-3554252594471363487213149204025130000000000000)
      constant := (119247458661044063336678771525834943863389768813) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree126.table
  base := (55433881963241298346637408505653047224039/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-3558132952430694126038134353096130000000000000)
      constant := (119502687807392505283102243282072060755793247559) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 126 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 126 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel126

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22338825339777588329/4000000000000000000)
  centralHi := (279235316747219854113/50000000000000000000)
  directionLo := (560700066045551888103/100000000000000000000)
  directionHi := (70087508255693986013/12500000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree127.table
  base := (1425652894029731649857144255548222352751/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-3582449862309166129341374620607730000000000000)
      constant := (121178015168536811280899252335579086023620657240) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree127.table
  base := (57026115759797910517372859873441241526777/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (3428871138)
      previous := (1714435569)
      next := (1714435569)
      square := (11921623758451521662001873490833300000000000000)
      linear := (-1581585208391264731997252106450068430000000000000)
      constant := (53553854082925193008023701497096315520168835446417) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 127 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 127 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel127

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (560700066045551888103/100000000000000000000)
  centralHi := (70087508255693986013/12500000000000000000)
  directionLo := (28146033452837173081/5000000000000000000)
  directionHi := (562920669056743461621/100000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree128.table
  base := (58638367808845902745774223723812757728099/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-3610647130146968771469600037190330000000000000)
      constant := (123124151845392507300191249706726905070321092419) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree128.table
  base := (5863836780766311566355136247213594761191/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (3428871138)
      previous := (1714435569)
      next := (1714435569)
      square := (11921623758451521662001873490833300000000000000)
      linear := (-1594033784760593354411686963184743530000000000000)
      constant := (54413907871306103076378313574882099354487405753110) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 128 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 128 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel128

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28146033452837173081/5000000000000000000)
  centralHi := (562920669056743461621/100000000000000000000)
  directionLo := (282566273305527893719/50000000000000000000)
  directionHi := (565132546611055787439/100000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree129.table
  base := (15067659526934282589999292093606509257281/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-3638844397984771413597825453772930000000000000)
      constant := (125085868691606316832202259421184973723469165444) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree129.table
  base := (60270638106731708005620438510094529556673/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (380985682)
      previous := (190492841)
      next := (190492841)
      square := (1324624862050169073555763721203700000000000000)
      linear := (-178498040125546886314013535546602070000000000000)
      constant := (6142316298688977602467705656078371898132686632337) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 129 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 129 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel129

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel130
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (282566273305527893719/50000000000000000000)
  centralHi := (565132546611055787439/100000000000000000000)
  directionLo := (283667900381283266463/50000000000000000000)
  directionHi := (567335800762566532927/100000000000000000000)

def endpointA : IntegerEndpointWitness 130 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree130.table
  base := (7740365832223405195339203282449880581919/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-3667041665822574055726050870355530000000000000)
      constant := (127063165707174932907486161322684445869590430712) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 130 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree130.table
  base := (61922926656932638580203325507066119983981/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (3428871138)
      previous := (1714435569)
      next := (1714435569)
      square := (11921623758451521662001873490833300000000000000)
      linear := (-1618930937499250599240556676654093730000000000000)
      constant := (56154670533607910406528569666968230087475940860901) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 130 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 130 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel130

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel131
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (283667900381283266463/50000000000000000000)
  centralHi := (567335800762566532927/100000000000000000000)
  directionLo := (284765265795667236879/50000000000000000000)
  directionHi := (569530531591334473759/100000000000000000000)

def endpointA : IntegerEndpointWitness 131 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree131.table
  base := (63595233458949556000238787706363139021749/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-3695238933660376697854276286938130000000000000)
      constant := (129056042892096316481513649239900378275609018069) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 131 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree131.table
  base := (15898808364555797890293885420204253855047/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (3428871138)
      previous := (1714435569)
      next := (1714435569)
      square := (11921623758451521662001873490833300000000000000)
      linear := (-1631379513868579221654991533388768830000000000000)
      constant := (57035379407526616180665553783140928440301031324348) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 131 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 131 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel131

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel132
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (284765265795667236879/50000000000000000000)
  centralHi := (569530531591334473759/100000000000000000000)
  directionLo := (142929209314111482601/25000000000000000000)
  directionHi := (114343367451289186081/20000000000000000000)

def endpointA : IntegerEndpointWitness 132 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree132.table
  base := (16321889627800355446746304733255966849231/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (64258)
      previous := (32129)
      next := (32129)
      square := (223414549173582235377932825300000000000000)
      linear := (-30772200012381647437871914905130000000000000)
      constant := (1083177687986524612374135359320781616130289564) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 132 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree132.table
  base := (65287558510584088865734943851230434872063/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 176890000000000000000000000000000000000000000
      center := (3148642)
      previous := (1574321)
      next := (1574321)
      square := (10947312909505529533518708439700000000000000)
      linear := (-1509484013074295540926929651169370000000000000)
      constant := (53189139862219049021784224967545355162451922407) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 132 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 132 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel132

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel133
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (142929209314111482601/25000000000000000000)
  centralHi := (114343367451289186081/20000000000000000000)
  directionLo := (573894814047242395773/100000000000000000000)
  directionHi := (286947407023621197887/50000000000000000000)

def endpointA : IntegerEndpointWitness 133 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree133.table
  base := (16749975453635003635618838877041528365759/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (21538)
      previous := (10769)
      next := (10769)
      square := (74884100969538643990941473300000000000000)
      linear := (-10392336480155074742688994792530000000000000)
      constant := (368666309612172560617708333918278099729027356) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 133 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree133.table
  base := (66999901814015376985428134538716472526821/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (193842)
      previous := (96921)
      next := (96921)
      square := (673956908725847795918473259700000000000000)
      linear := (-93633143004535952653279509687270000000000000)
      constant := (3325086338453145791977079387038622238581708069) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 133 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 133 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel133

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel134
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (573894814047242395773/100000000000000000000)
  centralHi := (286947407023621197887/50000000000000000000)
  directionLo := (576064556432804998081/100000000000000000000)
  directionHi := (288032278216402499041/50000000000000000000)

def endpointA : IntegerEndpointWitness 134 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree134.table
  base := (13746452673795761702688435425055184509929/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-3779830737173784624238952536685930000000000000)
      constant := (135128155462971353907252182725942997572891043245) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 134 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree134.table
  base := (34366131684266486445665602085091887481761/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (3428871138)
      previous := (1714435569)
      next := (1714435569)
      square := (11921623758451521662001873490833300000000000000)
      linear := (-1668725242976565088898296103592794130000000000000)
      constant := (59718816200350377383067349091467387756114087576562) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 134 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 134 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel134

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel135
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (576064556432804998081/100000000000000000000)
  centralHi := (288032278216402499041/50000000000000000000)
  directionLo := (289113078554883876391/50000000000000000000)
  directionHi := (578226157109767752783/100000000000000000000)

def endpointA : IntegerEndpointWitness 135 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree135.table
  base := (35242321587272307013670923297307927365551/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-3808028005011587266367177953268530000000000000)
      constant := (137183353325301827771962413669863465150509266462) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 135 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree135.table
  base := (27533063739908502024137949979994724223/3906250000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (380985682)
      previous := (190492841)
      next := (190492841)
      square := (1324624862050169073555763721203700000000000000)
      linear := (-186797091038432634590303440036385470000000000000)
      constant := (6736340576479460586824514808195510149399573214720) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 135 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 135 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel135

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel136
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (289113078554883876391/50000000000000000000)
  centralHi := (578226157109767752783/100000000000000000000)
  directionLo := (145094926762132018371/25000000000000000000)
  directionHi := (116075941409705614697/20000000000000000000)

def endpointA : IntegerEndpointWitness 136 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree136.table
  base := (72257041231275092098137171271790934582959/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-3836225272849389908495403369851130000000000000)
      constant := (139254131356987361047874310764359979813518232079) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 136 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree136.table
  base := (14451408246190636586550026299275673360543/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (3428871138)
      previous := (1714435569)
      next := (1714435569)
      square := (11921623758451521662001873490833300000000000000)
      linear := (-1693622395715222333727165817062144330000000000000)
      constant := (61542199204792759144288901326925880697176442716515) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 136 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 136 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel136

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel137
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (145094926762132018371/25000000000000000000)
  centralHi := (116075941409705614697/20000000000000000000)
  directionLo := (227548943569499891/39062500000000000)
  directionHi := (582525295537919720961/100000000000000000000)

def endpointA : IntegerEndpointWitness 137 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree137.table
  base := (74049457539216670984970121670689925603137/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-3864422540687192550623628786433730000000000000)
      constant := (141340489558029981767775454423449716640270627297) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 137 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree137.table
  base := (18512364384735789612230936478020987452799/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (3428871138)
      previous := (1714435569)
      next := (1714435569)
      square := (11921623758451521662001873490833300000000000000)
      linear := (-1706070972084550956141600673796819430000000000000)
      constant := (62464218249784142307044275307099286964160957941916) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 137 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 137 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel137

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel138
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (227548943569499891/39062500000000000)
  centralHi := (582525295537919720961/100000000000000000000)
  directionLo := (58466301022841025973/10000000000000000000)
  directionHi := (584663010228410259731/100000000000000000000)

def endpointA : IntegerEndpointWitness 138 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree138.table
  base := (75861892098422801295395550632197199798337/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-3892619808524995192751854203016330000000000000)
      constant := (143442427928432024707654448174075345884391158497) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 138 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree138.table
  base := (37930946049095210849621813849147967416389/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (380985682)
      previous := (190492841)
      next := (190492841)
      square := (1324624862050169073555763721203700000000000000)
      linear := (-190946616494875508728448392281277170000000000000)
      constant := (7043680258143372116738507416842825981742098215082) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 138 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 138 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel138

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel139
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58466301022841025973/10000000000000000000)
  centralHi := (584663010228410259731/100000000000000000000)
  directionLo := (293396468586941076023/50000000000000000000)
  directionHi := (586792937173882152047/100000000000000000000)

def endpointA : IntegerEndpointWitness 139 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree139.table
  base := (77694344908952496169727191614786601147157/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-3920817076362797834880079619598930000000000000)
      constant := (145559946468196067620493336207436463524708964917) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 139 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree139.table
  base := (77694344908755073988939169394825519105633/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (3428871138)
      previous := (1714435569)
      next := (1714435569)
      square := (11921623758451521662001873490833300000000000000)
      linear := (-1730968124823208200970470387266169630000000000000)
      constant := (64328911425312537125830928427513709683523441387193) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 139 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 139 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel139

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel140
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (293396468586941076023/50000000000000000000)
  centralHi := (586792937173882152047/100000000000000000000)
  directionLo := (117783032174410767771/20000000000000000000)
  directionHi := (73614395109006729857/12500000000000000000)

def endpointA : IntegerEndpointWitness 140 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree140.table
  base := (9943351996358638933835437725321789389117/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-3949014344200600477008305036181530000000000000)
      constant := (147693045177324877953731523451792448658448157416) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 140 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree140.table
  base := (79546815970701396658437223925151926506327/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3931290000000000000000000000000000000000000000
      center := (69976962)
      previous := (34988481)
      next := (34988481)
      square := (243298444050031054326568846751700000000000000)
      linear := (-35579932677398710681324596816343770000000000000)
      constant := (1332073174609223363361067613872834351715505827183) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 140 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 140 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel140

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel141
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117783032174410767771/20000000000000000000)
  centralHi := (73614395109006729857/12500000000000000000)
  directionLo := (591029764303594526897/100000000000000000000)
  directionHi := (295514882151797263449/50000000000000000000)

def endpointA : IntegerEndpointWitness 141 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree141.table
  base := (40709652642119663988317915186852463769203/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-3977211612038403119136530452764130000000000000)
      constant := (149841724055821368390449048810593834939805112486) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 141 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree141.table
  base := (16283861056819371509084656905009178161481/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (380985682)
      previous := (190492841)
      next := (190492841)
      square := (1324624862050169073555763721203700000000000000)
      linear := (-195096141951318382866593344526168870000000000000)
      constant := (7357904968323319082427248029066103868261554632445) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 141 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 141 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel141

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel142
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (591029764303594526897/100000000000000000000)
  centralHi := (295514882151797263449/50000000000000000000)
  directionLo := (593136828969983911319/100000000000000000000)
  directionHi := (14828420724249597783/2500000000000000000)

def endpointA : IntegerEndpointWitness 142 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree142.table
  base := (1301747075767692242858410162137457925451/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-4005408879876205761264755869346730000000000000)
      constant := (152005983103688559814925633548677343177064008384) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 142 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree142.table
  base := (10413976606126410475440932069418725308987/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (3428871138)
      previous := (1714435569)
      next := (1714435569)
      square := (11921623758451521662001873490833300000000000000)
      linear := (-1768313853931194068213774957470194930000000000000)
      constant := (67177588902487663040164579007821592222302726126616) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 142 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 142 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel142

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel143
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (593136828969983911319/100000000000000000000)
  centralHi := (14828420724249597783/2500000000000000000)
  directionLo := (595236434930165705583/100000000000000000000)
  directionHi := (37202277183135356599/6250000000000000000)

def endpointA : IntegerEndpointWitness 143 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree143.table
  base := (21306084666404742056867634515550625453349/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (64258)
      previous := (32129)
      next := (32129)
      square := (223414549173582235377932825300000000000000)
      linear := (-33335587997636433085892407321730000000000000)
      constant := (1274262994387847524983632431177145103154635956) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 143 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree143.table
  base := (85224338665516174609738289279503007830333/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1592010000000000000000000000000000000000000000
      center := (28337778)
      previous := (14168889)
      next := (14168889)
      square := (98525816185549765801668375957300000000000000)
      linear := (-14717044878516716451472808381858430000000000000)
      constant := (563148083624683438109486938481279348349596843933) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 143 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 143 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel143

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel144
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (595236434930165705583/100000000000000000000)
  centralHi := (37202277183135356599/6250000000000000000)
  directionLo := (298664330418020808607/50000000000000000000)
  directionHi := (119465732167208323443/20000000000000000000)

def endpointA : IntegerEndpointWitness 144 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree144.table
  base := (1361826292715178744061408293319308284549/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-4061803415551811045521206702511930000000000000)
      constant := (156381241707547490683166294442423885131352631616) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 144 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree144.table
  base := (17431376546736826291349615813047641046237/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (380985682)
      previous := (190492841)
      next := (190492841)
      square := (1324624862050169073555763721203700000000000000)
      linear := (-199245667407761257004738296771060570000000000000)
      constant := (7679014707023152133439340529554814512092466207265) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 144 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 144 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel144

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel145
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (298664330418020808607/50000000000000000000)
  centralHi := (119465732167208323443/20000000000000000000)
  directionLo := (299706791983425145797/50000000000000000000)
  directionHi := (119882716793370058319/20000000000000000000)

def endpointA : IntegerEndpointWitness 145 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree145.table
  base := (89109445053662539192951986376811333056907/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-4090000683389613687649432119094530000000000000)
      constant := (158592241263545561210112111953334845839258754667) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 145 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree145.table
  base := (44554722526794193618683538584163668904363/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (3428871138)
      previous := (1714435569)
      next := (1714435569)
      square := (11921623758451521662001873490833300000000000000)
      linear := (-1805659583039179935457079527674220230000000000000)
      constant := (70088231636354093318004977099127768641284925539046) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 145 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 145 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel145

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel146
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (299706791983425145797/50000000000000000000)
  centralHi := (119882716793370058319/20000000000000000000)
  directionLo := (601491280262473739691/100000000000000000000)
  directionHi := (150372820065618434923/25000000000000000000)

def endpointA : IntegerEndpointWitness 146 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree146.table
  base := (1821640512507307870217898302428882600863/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-4118197951227416329777657535677130000000000000)
      constant := (160818820988926956345314733895527981044414835150) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 146 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree146.table
  base := (91082025625302418288270949938200931958467/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (3428871138)
      previous := (1714435569)
      next := (1714435569)
      square := (11921623758451521662001873490833300000000000000)
      linear := (-1818108159408508557871514384408895330000000000000)
      constant := (71072215938025283760659943989416093644815108488907) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 146 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 146 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel146

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel147
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (601491280262473739691/100000000000000000000)
  centralHi := (150372820065618434923/25000000000000000000)
  directionLo := (9430653505557997859/1562500000000000000)
  directionHi := (603561824355711862977/100000000000000000000)

def endpointA : IntegerEndpointWitness 147 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree147.table
  base := (23268656112238276669224898664032083360927/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-4146395219065218971905882952259730000000000000)
      constant := (163060980883694869349103448209423951733154609148) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 147 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree147.table
  base := (93074624448899626055989583776397933631861/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-4150922303351104717201698959509230000000000000)
      constant := (163408356617286518105544977266904048138973320341) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 147 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 147 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel147

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel148
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9430653505557997859/1562500000000000000)
  centralHi := (603561824355711862977/100000000000000000000)
  directionLo := (605625289603563883589/100000000000000000000)
  directionHi := (60562528960356388359/10000000000000000000)

def endpointA : IntegerEndpointWitness 148 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree148.table
  base := (1485738148820288946010136238296921840669/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-4174592486903021614034108368842330000000000000)
      constant := (165318720947852480803420968663436701947024805696) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 148 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree148.table
  base := (95087241524453077152005531245846302323287/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (3428871138)
      previous := (1714435569)
      next := (1714435569)
      square := (11921623758451521662001873490833300000000000000)
      linear := (-1843005312147165802700384097878245530000000000000)
      constant := (73060839626949712995252520750912597378316523256127) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 148 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 148 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel148

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel149
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (605625289603563883589/100000000000000000000)
  centralHi := (60562528960356388359/10000000000000000000)
  directionLo := (37980109257347110921/6250000000000000000)
  directionHi := (607681748117553774737/100000000000000000000)

def endpointA : IntegerEndpointWitness 149 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree149.table
  base := (97119876852073857030606073436826078077337/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-4202789754740824256162333785424930000000000000)
      constant := (167592041181402949103004349829654269916496157497) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 149 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree149.table
  base := (97119876852035292337501015512629213651499/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (3428871138)
      previous := (1714435569)
      next := (1714435569)
      square := (11921623758451521662001873490833300000000000000)
      linear := (-1855453888516494425114818954612920630000000000000)
      constant := (74065479014205756283483318822381726616546407368179) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 149 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 149 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel149

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel150
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37980109257347110921/6250000000000000000)
  centralHi := (607681748117553774737/100000000000000000000)
  directionLo := (609731270793135159723/100000000000000000000)
  directionHi := (152432817698283789931/25000000000000000000)

def endpointA : IntegerEndpointWitness 150 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree150.table
  base := (9917253043175082238806573407614954050067/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-4230987022578626898290559202007530000000000000)
      constant := (169880941584349402779499730279509788078609766270) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 150 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree150.table
  base := (49586265215859038236724284052769193152239/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (380985682)
      previous := (190492841)
      next := (190492841)
      square := (1324624862050169073555763721203700000000000000)
      linear := (-207544718320647005281028201260843970000000000000)
      constant := (8341889269999207505480444826237089840356129272382) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 150 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 150 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel150

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel151
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (609731270793135159723/100000000000000000000)
  centralHi := (152432817698283789931/25000000000000000000)
  directionLo := (611773927338209603347/100000000000000000000)
  directionHi := (152943481834552400837/25000000000000000000)

def endpointA : IntegerEndpointWitness 151 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree151.table
  base := (101245202263600186590545995618000912850089/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-4259184290416429540418784618590130000000000000)
      constant := (172185422156694934359188362632831227874204737609) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 151 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree151.table
  base := (50622601131786191366022466138066405848801/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (3428871138)
      previous := (1714435569)
      next := (1714435569)
      square := (11921623758451521662001873490833300000000000000)
      linear := (-1880351041255151669943688668082270830000000000000)
      constant := (76095412874312413586506568732578207820363462256242) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 151 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 151 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel151

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel152
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (611773927338209603347/100000000000000000000)
  centralHi := (152943481834552400837/25000000000000000000)
  directionLo := (153452446575197687917/25000000000000000000)
  directionHi := (613809786300790751669/100000000000000000000)

def endpointA : IntegerEndpointWitness 152 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree152.table
  base := (103337892347691812056400399599277779997827/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (21538)
      previous := (10769)
      next := (10769)
      square := (74884100969538643990941473300000000000000)
      linear := (-11876403208460476959964016717930000000000000)
      constant := (483394689469370070643674094009672611379737067) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 152 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree152.table
  base := (20667578469533641085552492998876963725217/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 533610000000000000000000000000000000000000000
      center := (9498258)
      previous := (4749129)
      next := (4749129)
      square := (33023888527566542000005189725300000000000000)
      linear := (-5243212237186926017612530539659130000000000000)
      constant := (213630768274697348249248949223418528306706521685) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 152 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 152 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel152

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel153
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (153452446575197687917/25000000000000000000)
  centralHi := (613809786300790751669/100000000000000000000)
  directionLo := (7697986438698067267/1250000000000000000)
  directionHi := (615838915095845381361/100000000000000000000)

def endpointA : IntegerEndpointWitness 153 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree153.table
  base := (843604805472756310884868420279724112251/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-4315578826092034824675235451755330000000000000)
      constant := (176841123809595393212348870385672618618404491375) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 153 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree153.table
  base := (5272530034203724836079440913968109511329/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (380985682)
      previous := (190492841)
      next := (190492841)
      square := (1324624862050169073555763721203700000000000000)
      linear := (-211694243777089879419173153505735670000000000000)
      constant := (8683654094283798132372406451693450231733074808020) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 153 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 153 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel153

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel154
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7697986438698067267/1250000000000000000)
  centralHi := (615838915095845381361/100000000000000000000)
  directionLo := (617861380031341093661/100000000000000000000)
  directionHi := (308930690015670546831/50000000000000000000)

def endpointA : IntegerEndpointWitness 154 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree154.table
  base := (2151666545457522367004427993055071682353/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (64258)
      previous := (32129)
      next := (32129)
      square := (223414549173582235377932825300000000000000)
      linear := (-35898975982891218733912899738330000000000000)
      constant := (1480928470166580883766334399304664043866471650) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 154 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree154.table
  base := (6723957954553693950408150021183285077717/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32490000000000000000000000000000000000000000
      center := (578322)
      previous := (289161)
      next := (289161)
      square := (2010730942562240118401395427700000000000000)
      linear := (-323443543660505572134760202105970000000000000)
      constant := (13356713000249458923481998602749921891480040528) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 154 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 154 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel154

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel155
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (617861380031341093661/100000000000000000000)
  centralHi := (308930690015670546831/50000000000000000000)
  directionLo := (77484655791691140841/12500000000000000000)
  directionHi := (619877246333529126729/100000000000000000000)

def endpointA : IntegerEndpointWitness 155 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree155.table
  base := (54868036057051581864681894619832665071609/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-4371973361767640108931686284920530000000000000)
      constant := (181559146140128186403868501226092471285985905458) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 155 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree155.table
  base := (54868036057044359509125327897786412821871/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (3428871138)
      previous := (1714435569)
      next := (1714435569)
      square := (11921623758451521662001873490833300000000000000)
      linear := (-1930145346732466159601428095020971230000000000000)
      constant := (80237900936941603766442308102772289369252433787182) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 155 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 155 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel155

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel156
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (77484655791691140841/12500000000000000000)
  centralHi := (619877246333529126729/100000000000000000000)
  directionLo := (124377315634297912051/20000000000000000000)
  directionHi := (9716977783929524379/1562500000000000000)

def endpointA : IntegerEndpointWitness 156 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree156.table
  base := (55954417603920557363507384106017009192757/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-4400170629605442751059911701503130000000000000)
      constant := (183941527559513950089576520864709337957097637034) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 156 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree156.table
  base := (55954417603914426325211310688385733439343/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (380985682)
      previous := (190492841)
      next := (190492841)
      square := (1324624862050169073555763721203700000000000000)
      linear := (-215843769233532753557318105750627370000000000000)
      constant := (9032303947104792281094013711330162187791666275134) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 156 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 156 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel156

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel157
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (124377315634297912051/20000000000000000000)
  centralHi := (9716977783929524379/1562500000000000000)
  directionLo := (623889438680965044297/100000000000000000000)
  directionHi := (311944719340482522149/50000000000000000000)

def endpointA : IntegerEndpointWitness 157 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree157.table
  base := (7131351034634638370124753638487664659137/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-4428367897443245393188137118085730000000000000)
      constant := (186339489148316384172936032854931384879612212752) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 157 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree157.table
  base := (28525404138535951276425010012627397617473/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (3428871138)
      previous := (1714435569)
      next := (1714435569)
      square := (11921623758451521662001873490833300000000000000)
      linear := (-1955042499471123404430297808490321430000000000000)
      constant := (82350455139484860898390956515945510614800070431332) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 157 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 157 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel157

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel158
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (623889438680965044297/100000000000000000000)
  centralHi := (311944719340482522149/50000000000000000000)
  directionLo := (625885889987508097087/100000000000000000000)
  directionHi := (9779467031054814017/1562500000000000000)

def endpointA : IntegerEndpointWitness 158 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree158.table
  base := (930515329224843941505593401047083461221/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-4456565165281048035316362534668330000000000000)
      constant := (188753030906538241927389992501909146583699312625) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 158 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree158.table
  base := (116314416153096657393394884030860607625981/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (3428871138)
      previous := (1714435569)
      next := (1714435569)
      square := (11921623758451521662001873490833300000000000000)
      linear := (-1967491075840452026844732665224996530000000000000)
      constant := (83417059783568010021808187954597218980954319942901) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 158 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 158 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel158

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel159
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (625885889987508097087/100000000000000000000)
  centralHi := (9779467031054814017/1562500000000000000)
  directionLo := (125575198645793196273/20000000000000000000)
  directionHi := (313937996614482990683/50000000000000000000)

def endpointA : IntegerEndpointWitness 159 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree159.table
  base := (59273617002378382525227959421616689823869/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-4484762433118850677444587951250930000000000000)
      constant := (191182152834182223451357077656460847256392843578) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 159 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree159.table
  base := (118547234004749265705158093868306082090487/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (380985682)
      previous := (190492841)
      next := (190492841)
      square := (1324624862050169073555763721203700000000000000)
      linear := (-219993294689975627695463057995519070000000000000)
      constant := (9387838828465974383974825256189158650617933569703) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 159 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 159 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel159

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel160
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (125575198645793196273/20000000000000000000)
  centralHi := (313937996614482990683/50000000000000000000)
  directionLo := (314929904288663091267/50000000000000000000)
  directionHi := (125971961715465236507/20000000000000000000)

def endpointA : IntegerEndpointWitness 160 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree160.table
  base := (15100008763646078502150899131450377600151/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-4512959700956653319572813367833530000000000000)
      constant := (193626854931250975682762995433051871551617566648) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 160 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree160.table
  base := (120800070109162262869610942552558550387371/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (3428871138)
      previous := (1714435569)
      next := (1714435569)
      square := (11921623758451521662001873490833300000000000000)
      linear := (-1992388228579109271673602378694346730000000000000)
      constant := (85570924157363307189927544138290599527406601919091) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 160 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 160 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel160

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel161
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (314929904288663091267/50000000000000000000)
  centralHi := (125971961715465236507/20000000000000000000)
  directionLo := (631837395259944572177/100000000000000000000)
  directionHi := (315918697629972286089/50000000000000000000)

def endpointA : IntegerEndpointWitness 161 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree161.table
  base := (61536462233200233594174716253630077774751/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-4541156968794455961701038784416130000000000000)
      constant := (196087137197747092643996821998052260854557796862) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 161 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree161.table
  base := (123072924466395064913906738860082582323677/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3931290000000000000000000000000000000000000000
      center := (69976962)
      previous := (34988481)
      next := (34988481)
      square := (243298444050031054326568846751700000000000000)
      linear := (-40915036835682406001796678274061670000000000000)
      constant := (1768534365042403423964778313378263025506324815333) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 161 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 161 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel161

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel162
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (631837395259944572177/100000000000000000000)
  centralHi := (315918697629972286089/50000000000000000000)
  directionLo := (316904405790088722359/50000000000000000000)
  directionHi := (633808811580177444719/100000000000000000000)

def endpointA : IntegerEndpointWitness 162 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree162.table
  base := (62682898538255233316083095398873327114173/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-4569354236632258603829264200998730000000000000)
      constant := (198562999633673115873345251255719431603348381626) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 162 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree162.table
  base := (62682898538252940875655889794745719980583/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (380985682)
      previous := (190492841)
      next := (190492841)
      square := (1324624862050169073555763721203700000000000000)
      linear := (-224142820146418501833608010240410770000000000000)
      constant := (9750258738370919169450870865683139293858240910254) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 162 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 162 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel162

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel163
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (316904405790088722359/50000000000000000000)
  centralHi := (633808811580177444719/100000000000000000000)
  directionLo := (158943528734359440217/25000000000000000000)
  directionHi := (635774114937437760869/100000000000000000000)

def endpointA : IntegerEndpointWitness 163 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree163.table
  base := (12767868793955562218984482598376670968199/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-4597551504470061245957489617581330000000000000)
      constant := (201054442239031535006147188193503003645619005190) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 163 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree163.table
  base := (63839343969775865587362968054509287782693/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (3428871138)
      previous := (1714435569)
      next := (1714435569)
      square := (11921623758451521662001873490833300000000000000)
      linear := (-2029733957687095138916906948898372030000000000000)
      constant := (88853358432145919794325987188155685906078787006906) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 163 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 163 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel163

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel164
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (158943528734359440217/25000000000000000000)
  centralHi := (635774114937437760869/100000000000000000000)
  directionLo := (318866680923347558447/50000000000000000000)
  directionHi := (127546672369339023379/20000000000000000000)

def endpointA : IntegerEndpointWitness 164 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree164.table
  base := (16251449631948969688074067062591674969381/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-4625748772307863888085715034163930000000000000)
      constant := (203561465013824788474961566446260255634700251688) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 164 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree164.table
  base := (65005798527794227735688533799468141154103/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (3428871138)
      previous := (1714435569)
      next := (1714435569)
      square := (11921623758451521662001873490833300000000000000)
      linear := (-2042182534056423761331341805633047130000000000000)
      constant := (89961273247501785289982829998089567084649593112126) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 164 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 164 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel164

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel165
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (318866680923347558447/50000000000000000000)
  centralHi := (127546672369339023379/20000000000000000000)
  directionLo := (639686607957438181523/100000000000000000000)
  directionHi := (159921651989359545381/25000000000000000000)

def endpointA : IntegerEndpointWitness 165 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree165.table
  base := (132364524424673542188899050067351121747797/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (64258)
      previous := (32129)
      next := (32129)
      square := (223414549173582235377932825300000000000000)
      linear := (-38462363968146004381933392154930000000000000)
      constant := (1703174115355828630604392973640263754950954717) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 165 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree165.table
  base := (26472904884934148017546621231830898876379/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 176890000000000000000000000000000000000000000
      center := (3148642)
      previous := (1574321)
      next := (1574321)
      square := (10947312909505529533518708439700000000000000)
      linear := (-1886713600023647735303743491614070000000000000)
      constant := (83632757659694143650447847854175083851121340655) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 165 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 165 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel165

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel166
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (639686607957438181523/100000000000000000000)
  centralHi := (159921651989359545381/25000000000000000000)
  directionLo := (128326781614423520123/20000000000000000000)
  directionHi := (80204238509014700077/12500000000000000000)

def endpointA : IntegerEndpointWitness 166 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree166.table
  base := (134737470046854511641499899034312973220989/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-4682143307983469172342165867329130000000000000)
      constant := (208622251071725300970409305074748604983266020509) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 166 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree166.table
  base := (134737470046852133869365056838848336172447/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (3428871138)
      previous := (1714435569)
      next := (1714435569)
      square := (11921623758451521662001873490833300000000000000)
      linear := (-2067079686795081006160211519102397330000000000000)
      constant := (92197757963862362758992029832031864800005757916487) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 166 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 166 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel166

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel167
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (128326781614423520123/20000000000000000000)
  centralHi := (80204238509014700077/12500000000000000000)
  directionLo := (160893829041021665411/25000000000000000000)
  directionHi := (128715063232817332329/20000000000000000000)

def endpointA : IntegerEndpointWitness 167 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree167.table
  base := (137130433922187088107987882675931049556487/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-4710340575821271814470391283911730000000000000)
      constant := (211176014354837188332904571304191554175676908647) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 167 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree167.table
  base := (68565216961092535240458164500340594176921/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (3428871138)
      previous := (1714435569)
      next := (1714435569)
      square := (11921623758451521662001873490833300000000000000)
      linear := (-2079528263164409628574646375837072430000000000000)
      constant := (93326327864869116307459032899682552659921520029282) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 167 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 167 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel167

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel168
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (160893829041021665411/25000000000000000000)
  centralHi := (128715063232817332329/20000000000000000000)
  directionLo := (64551088539505633397/10000000000000000000)
  directionHi := (645510885395056333971/100000000000000000000)

def endpointA : IntegerEndpointWitness 168 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree168.table
  base := (139543416050722602648257771246605395240707/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-4738537843659074456598616700494330000000000000)
      constant := (213745357807393168582644611958283210269509322467) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 168 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree168.table
  base := (69771708025360445339447027269485278856147/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-4743711654271515308365263565922330000000000000)
      constant := (214199053955619437810003844073964412931430714214) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 168 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 168 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel168

namespace ForestUnimodality.Stage130KernelData.Cell114.Kernel169
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64551088539505633397/10000000000000000000)
  centralHi := (645510885395056333971/100000000000000000000)
  directionLo := (647440668132080655067/100000000000000000000)
  directionHi := (161860167033020163767/25000000000000000000)

def endpointA : IntegerEndpointWitness 169 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree169.table
  base := (70988208216255658866061096316297018533629/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (27033160450003450480729871861300000000000000)
      linear := (-4766735111496877098726842117076930000000000000)
      constant := (216330281429395437234573312435723210133134896698) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 169 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree169.table
  base := (70988208216254932583362088090720280920217/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (3428871138)
      previous := (1714435569)
      next := (1714435569)
      square := (11921623758451521662001873490833300000000000000)
      linear := (-2104425415903066873403516089306422630000000000000)
      constant := (95604122752540498439947006577330890405152630921314) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 169 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 169 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell114.Kernel169
