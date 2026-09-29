import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage80KernelData.Cell076.Parameters
import ForestUnimodality.BinomialMassData.Q3193_6468.Batch000_049
import ForestUnimodality.BinomialMassData.Q3193_6468.Batch050_099
import ForestUnimodality.BinomialMassData.Q49_99.Batch000_049
import ForestUnimodality.BinomialMassData.Q49_99.Batch050_099

namespace ForestUnimodality.Stage80KernelData.Cell076.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree000.table
  base := (388981083851720087951520101/10000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (78)
      previous := (39)
      next := (39)
      square := (1032441989066586740531050700000000000000)
      linear := (13425840787084182201271965000000000000)
      constant := (388981083851720087951520101000000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree000.table
  base := (388981083851720087951520101/10000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (78)
      previous := (39)
      next := (39)
      square := (1032441989066586740531050700000000000000)
      linear := (13425840787084182201271965000000000000)
      constant := (388981083851720087951520101000000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree000.checked
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
end ForestUnimodality.Stage80KernelData.Cell076.Kernel000

namespace ForestUnimodality.Stage80KernelData.Cell076.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree001.table
  base := (115260923842103509067090464291311003888087/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 48510000000000000000000000000000000000000000
      center := (378378)
      previous := (189189)
      next := (189189)
      square := (5008376088962012278316126945700000000000000)
      linear := (-4879752152976271825915097025435000000000000)
      constant := (1119449879259720185118925222620721859722220074) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree001.table
  base := (14381778577277093812036046608768480206687/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8910000000000000000000000000000000000000000
      center := (69498)
      previous := (34749)
      next := (34749)
      square := (919905812258328785813166173700000000000000)
      linear := (-898651410215437498807053396585000000000000)
      constant := (205246068530579588420400124311738453826529872) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree001.checked
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
end ForestUnimodality.Stage80KernelData.Cell076.Kernel001

namespace ForestUnimodality.Stage80KernelData.Cell076.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (12498995418557205427/25000000000000000000)
  directionHi := (49995981674228821709/100000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree002.table
  base := (34984738537788762171730602805127174189389/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 48510000000000000000000000000000000000000000
      center := (378378)
      previous := (189189)
      next := (189189)
      square := (5008376088962012278316126945700000000000000)
      linear := (-9824633059610689019688564353085000000000000)
      constant := (683661754226230641470967761172745187970904156) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree002.table
  base := (8716678669210020623331844469879350766489/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8910000000000000000000000000000000000000000
      center := (69498)
      previous := (34749)
      next := (34749)
      square := (919905812258328785813166173700000000000000)
      linear := (-1809265244572167003955440113985000000000000)
      constant := (125154545231501618398977272064270024527067184) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree002.checked
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
end ForestUnimodality.Stage80KernelData.Cell076.Kernel002

namespace ForestUnimodality.Stage80KernelData.Cell076.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12498995418557205427/25000000000000000000)
  centralHi := (49995981674228821709/100000000000000000000)
  directionLo := (70704995347851118773/100000000000000000000)
  directionHi := (35352497673925559387/50000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree003.table
  base := (43765190458473199229214681753940283016713/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5390000000000000000000000000000000000000000
      center := (42042)
      previous := (21021)
      next := (21021)
      square := (556486232106890253146236327300000000000000)
      linear := (-1641057107360567357051336853415000000000000)
      constant := (48388705812682628815991295689292625092016614) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree003.table
  base := (21780275375709311629667887477800822030489/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (702)
      previous := (351)
      next := (351)
      square := (9291977901599280664779456300000000000000)
      linear := (-27473526049786833425291180115000000000000)
      constant := (804397216262693562811809205095829593097604) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree003.checked
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
end ForestUnimodality.Stage80KernelData.Cell076.Kernel003

namespace ForestUnimodality.Stage80KernelData.Cell076.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70704995347851118773/100000000000000000000)
  centralHi := (35352497673925559387/50000000000000000000)
  directionLo := (21648895108511705121/25000000000000000000)
  directionHi := (17319116086809364097/20000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree004.table
  base := (14165507616728941629885797599565428172047/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (34398)
      previous := (17199)
      next := (17199)
      square := (455306917178364752574193358700000000000000)
      linear := (-1792217715716320309748681728035000000000000)
      constant := (26751606043619805811858052558448415295490908) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree004.table
  base := (56340882721963152942633600383805640491877/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8910000000000000000000000000000000000000000
      center := (69498)
      previous := (34749)
      next := (34749)
      square := (919905812258328785813166173700000000000000)
      linear := (-3630492913285626014252213548785000000000000)
      constant := (53781706181391843340323570894910825678262407) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree004.checked
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
end ForestUnimodality.Stage80KernelData.Cell076.Kernel004

namespace ForestUnimodality.Stage80KernelData.Cell076.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21648895108511705121/25000000000000000000)
  centralHi := (17319116086809364097/20000000000000000000)
  directionLo := (12498995418557205427/12500000000000000000)
  directionHi := (99991963348457643417/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree005.table
  base := (1520619325088774157155211230268045443013/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 48510000000000000000000000000000000000000000
      center := (378378)
      previous := (189189)
      next := (189189)
      square := (5008376088962012278316126945700000000000000)
      linear := (-24659275779513940601008966336035000000000000)
      constant := (214766042885436986565866614374994711101401575) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree005.table
  base := (37773003909391470068850119719532051973799/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8910000000000000000000000000000000000000000
      center := (69498)
      previous := (34749)
      next := (34749)
      square := (919905812258328785813166173700000000000000)
      linear := (-4541106747642355519400600266185000000000000)
      constant := (39259990721943358218716771829778058308654909) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree005.checked
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
end ForestUnimodality.Stage80KernelData.Cell076.Kernel005

namespace ForestUnimodality.Stage80KernelData.Cell076.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12498995418557205427/12500000000000000000)
  centralHi := (99991963348457643417/100000000000000000000)
  directionLo := (55897206812704695447/50000000000000000000)
  directionHi := (22358882725081878179/20000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree006.table
  base := (26351722593841828865484517828332102663157/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 770000000000000000000000000000000000000000
      center := (6006)
      previous := (3003)
      next := (3003)
      square := (79498033158127179020890903900000000000000)
      linear := (-469907248986481869758451327995000000000000)
      constant := (2723476403813057977567422976539071905063089) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree006.table
  base := (5233915778702374335524179353916686478447/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 990000000000000000000000000000000000000000
      center := (7722)
      previous := (3861)
      next := (3861)
      square := (102211756917592087312574019300000000000000)
      linear := (-605746731333231669394331887065000000000000)
      constant := (3488256828084045187977313997278759806831265) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree006.checked
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
end ForestUnimodality.Stage80KernelData.Cell076.Kernel006

namespace ForestUnimodality.Stage80KernelData.Cell076.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55897206812704695447/50000000000000000000)
  centralHi := (22358882725081878179/20000000000000000000)
  directionLo := (122464644291399242379/100000000000000000000)
  directionHi := (6123232214569962119/5000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree007.table
  base := (18727747418882396537170413991765955330577/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6930000000000000000000000000000000000000000
      center := (54054)
      previous := (27027)
      next := (27027)
      square := (715482298423144611188018135100000000000000)
      linear := (-4935576798968967855507985855905000000000000)
      constant := (21490011160058300922312839590353807044089861) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree007.table
  base := (18588523865924441552535025584512667791893/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8910000000000000000000000000000000000000000
      center := (69498)
      previous := (34749)
      next := (34749)
      square := (919905812258328785813166173700000000000000)
      linear := (-6362334416355814529697373700985000000000000)
      constant := (27563271700546663410738616131145787002576663) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree007.checked
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
end ForestUnimodality.Stage80KernelData.Cell076.Kernel007

namespace ForestUnimodality.Stage80KernelData.Cell076.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122464644291399242379/100000000000000000000)
  centralHi := (6123232214569962119/5000000000000000000)
  directionLo := (132276934062552149927/100000000000000000000)
  directionHi := (16534616757819018741/12500000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree008.table
  base := (539344827543225972455870279839576383759/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 48510000000000000000000000000000000000000000
      center := (378378)
      previous := (189189)
      next := (189189)
      square := (5008376088962012278316126945700000000000000)
      linear := (-39493918499417192182329368318985000000000000)
      constant := (143266882957341610748735882576874625940372725) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree008.table
  base := (1337367457759197054607770367972174986157/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8910000000000000000000000000000000000000000
      center := (69498)
      previous := (34749)
      next := (34749)
      square := (919905812258328785813166173700000000000000)
      linear := (-7272948250712544034845760418385000000000000)
      constant := (26291229119421975025109453282912079126658870) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree008.checked
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
end ForestUnimodality.Stage80KernelData.Cell076.Kernel008

namespace ForestUnimodality.Stage80KernelData.Cell076.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132276934062552149927/100000000000000000000)
  centralHi := (16534616757819018741/12500000000000000000)
  directionLo := (70704995347851118773/50000000000000000000)
  directionHi := (141409990695702237547/100000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree009.table
  base := (1209833924686898713964511769428831657619/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5390000000000000000000000000000000000000000
      center := (42042)
      previous := (21021)
      next := (21021)
      square := (556486232106890253146236327300000000000000)
      linear := (-4937644378450178819566981738515000000000000)
      constant := (16169581433736327367348785653049622107653128) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree009.table
  base := (9588271279706162262396858414959867510827/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 110000000000000000000000000000000000000000
      center := (858)
      previous := (429)
      next := (429)
      square := (11356861879732454145841557700000000000000)
      linear := (-101031630679867574567828976985000000000000)
      constant := (330167046582643820323507909979558542619097) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree009.checked
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
end ForestUnimodality.Stage80KernelData.Cell076.Kernel009

namespace ForestUnimodality.Stage80KernelData.Cell076.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70704995347851118773/50000000000000000000)
  centralHi := (141409990695702237547/100000000000000000000)
  directionLo := (37496986255671616281/25000000000000000000)
  directionHi := (1199903560181491721/800000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree010.table
  base := (6776090150865228404319283264828409455273/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 48510000000000000000000000000000000000000000
      center := (378378)
      previous := (189189)
      next := (189189)
      square := (5008376088962012278316126945700000000000000)
      linear := (-49383680312686026569876302974285000000000000)
      constant := (154604065585279524070091293196470114267529323) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree010.table
  base := (6698682002674915629780210802489459703229/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8910000000000000000000000000000000000000000
      center := (69498)
      previous := (34749)
      next := (34749)
      square := (919905812258328785813166173700000000000000)
      linear := (-9094175919426003045142533853185000000000000)
      constant := (28444710576956624619127037829368108595577039) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree010.checked
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
end ForestUnimodality.Stage80KernelData.Cell076.Kernel010

namespace ForestUnimodality.Stage80KernelData.Cell076.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37496986255671616281/25000000000000000000)
  centralHi := (1199903560181491721/800000000000000000)
  directionLo := (39525293986650372653/25000000000000000000)
  directionHi := (158101175946601490613/100000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree011.table
  base := (2233121347834447832297066271256604510171/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (34398)
      previous := (17199)
      next := (17199)
      square := (455306917178364752574193358700000000000000)
      linear := (-4938960110847313069422706391085000000000000)
      constant := (15363485930990023091499891563733325177970822) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree011.table
  base := (1099397173390067273798284267934982952227/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (6318)
      previous := (3159)
      next := (3159)
      square := (83627801114393525983015106700000000000000)
      linear := (-909526341252975686390083688235000000000000)
      constant := (2829177104140152436374935896945934476521548) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree011.checked
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
end ForestUnimodality.Stage80KernelData.Cell076.Kernel011

namespace ForestUnimodality.Stage80KernelData.Cell076.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39525293986650372653/25000000000000000000)
  centralHi := (158101175946601490613/100000000000000000000)
  directionLo := (20727239029862697319/12500000000000000000)
  directionHi := (165817912238901578553/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree012.table
  base := (320955097531895269612124161198494262199/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5390000000000000000000000000000000000000000
      center := (42042)
      previous := (21021)
      next := (21021)
      square := (556486232106890253146236327300000000000000)
      linear := (-6585938013994984550824804181065000000000000)
      constant := (20869852484633332534239363672542907258602088) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree012.table
  base := (125254390056075298496698763251025277861/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 990000000000000000000000000000000000000000
      center := (7722)
      previous := (3861)
      next := (3861)
      square := (102211756917592087312574019300000000000000)
      linear := (-1212822620904384672826589698665000000000000)
      constant := (3845772157199314157729192335017030050164780) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree012.checked
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
end ForestUnimodality.Stage80KernelData.Cell076.Kernel012

namespace ForestUnimodality.Stage80KernelData.Cell076.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (20727239029862697319/12500000000000000000)
  centralHi := (165817912238901578553/100000000000000000000)
  directionLo := (21648895108511705121/12500000000000000000)
  directionHi := (173191160868093640969/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree013.table
  base := (48569648704845285458832572421469355247/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6930000000000000000000000000000000000000000
      center := (54054)
      previous := (27027)
      next := (27027)
      square := (715482298423144611188018135100000000000000)
      linear := (-9174046147512754021599529279605000000000000)
      constant := (30080973516888810116919607336914065263723420) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree013.table
  base := (456662823602770234270686578950945615641/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8910000000000000000000000000000000000000000
      center := (69498)
      previous := (34749)
      next := (34749)
      square := (919905812258328785813166173700000000000000)
      linear := (-11826017422496191560587694005385000000000000)
      constant := (38821616757478677042596281443645585087072262) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree013.checked
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
end ForestUnimodality.Stage80KernelData.Cell076.Kernel013

namespace ForestUnimodality.Stage80KernelData.Cell076.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21648895108511705121/12500000000000000000)
  centralHi := (173191160868093640969/100000000000000000000)
  directionLo := (90131537746794981473/50000000000000000000)
  directionHi := (180263075493589962947/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree014.table
  base := (-48749034298069500814396833041243116551/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6930000000000000000000000000000000000000000
      center := (54054)
      previous := (27027)
      next := (27027)
      square := (715482298423144611188018135100000000000000)
      linear := (-9880457705603385049281453183555000000000000)
      constant := (33840767213392442866352946810226848161841256) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree014.table
  base := (-222266468274366357000755608673518694279/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (6318)
      previous := (3159)
      next := (3159)
      square := (83627801114393525983015106700000000000000)
      linear := (-1157875568804811005976007338435000000000000)
      constant := (3971854548962407349314085450784889971526802) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree014.checked
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
end ForestUnimodality.Stage80KernelData.Cell076.Kernel014

namespace ForestUnimodality.Stage80KernelData.Cell076.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (90131537746794981473/50000000000000000000)
  centralHi := (180263075493589962947/100000000000000000000)
  directionLo := (23383479267549109491/12500000000000000000)
  directionHi := (187067834140392875929/100000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree015.table
  base := (-1560158169453791312560308876837619808287/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (3822)
      previous := (1911)
      next := (1911)
      square := (50589657464262750286021484300000000000000)
      linear := (-748566513594526389280238783965000000000000)
      constant := (2692652796003927874892729036384956629393937) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree015.table
  base := (-322345774107684140179423508879633119407/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 990000000000000000000000000000000000000000
      center := (7722)
      previous := (3861)
      next := (3861)
      square := (102211756917592087312574019300000000000000)
      linear := (-1516360565689961174542718604465000000000000)
      constant := (5464419066449268485818370311329581605893535) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree015.checked
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
end ForestUnimodality.Stage80KernelData.Cell076.Kernel015

namespace ForestUnimodality.Stage80KernelData.Cell076.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23383479267549109491/12500000000000000000)
  centralHi := (187067834140392875929/100000000000000000000)
  directionLo := (96816802200789717329/50000000000000000000)
  directionHi := (193633604401579434659/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree016.table
  base := (-2568800472311745752817769277619471117119/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 48510000000000000000000000000000000000000000
      center := (378378)
      previous := (189189)
      next := (189189)
      square := (5008376088962012278316126945700000000000000)
      linear := (-79052965752492529732517106940185000000000000)
      constant := (299484529412561162634905795402527945610855731) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree016.table
  base := (-1308859672020957750212399656738787998177/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8910000000000000000000000000000000000000000
      center := (69498)
      previous := (34749)
      next := (34749)
      square := (919905812258328785813166173700000000000000)
      linear := (-14557858925566380076032854157585000000000000)
      constant := (55263485080202436352950556013851479787248586) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree016.checked
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
end ForestUnimodality.Stage80KernelData.Cell076.Kernel016

namespace ForestUnimodality.Stage80KernelData.Cell076.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96816802200789717329/50000000000000000000)
  centralHi := (193633604401579434659/100000000000000000000)
  directionLo := (12498995418557205427/6250000000000000000)
  directionHi := (199983926696915286833/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree017.table
  base := (-3437275366695488472313245430036209032003/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 48510000000000000000000000000000000000000000
      center := (378378)
      previous := (189189)
      next := (189189)
      square := (5008376088962012278316126945700000000000000)
      linear := (-83997846659126946926290574267835000000000000)
      constant := (335517479470955486703527870000976849985753447) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree017.table
  base := (-3483724543847828295541152805121900588713/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8910000000000000000000000000000000000000000
      center := (69498)
      previous := (34749)
      next := (34749)
      square := (919905812258328785813166173700000000000000)
      linear := (-15468472759923109581181240874985000000000000)
      constant := (61922633298634888220196282308331386575456717) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree017.checked
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
end ForestUnimodality.Stage80KernelData.Cell076.Kernel017

namespace ForestUnimodality.Stage80KernelData.Cell076.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12498995418557205427/6250000000000000000)
  centralHi := (199983926696915286833/100000000000000000000)
  directionLo := (206138713299290317851/100000000000000000000)
  directionHi := (51534678324822579463/25000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree018.table
  base := (-261362222047430844963474042313824926283/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5390000000000000000000000000000000000000000
      center := (42042)
      previous := (21021)
      next := (21021)
      square := (556486232106890253146236327300000000000000)
      linear := (-9882525285084596013340449066165000000000000)
      constant := (41621425463458376534623235548543073835735408) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree018.table
  base := (-1056470944018790996092505741711213630373/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 110000000000000000000000000000000000000000
      center := (858)
      previous := (429)
      next := (429)
      square := (11356861879732454145841557700000000000000)
      linear := (-202210945608393075139871945585000000000000)
      constant := (853615260883811587776224269594706600263588) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree018.checked
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
end ForestUnimodality.Stage80KernelData.Cell076.Kernel018

namespace ForestUnimodality.Stage80KernelData.Cell076.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (206138713299290317851/100000000000000000000)
  centralHi := (51534678324822579463/25000000000000000000)
  directionLo := (1325718662772208477/625000000000000000)
  directionHi := (212114986043553356321/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree019.table
  base := (-481526914965369369339403303923339123999/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 48510000000000000000000000000000000000000000
      center := (378378)
      previous := (189189)
      next := (189189)
      square := (5008376088962012278316126945700000000000000)
      linear := (-93887608472395781313837508923135000000000000)
      constant := (416647961227065813149894432764043819094808510) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree019.table
  base := (-2428534453428594382205215952007224495207/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8910000000000000000000000000000000000000000
      center := (69498)
      previous := (34749)
      next := (34749)
      square := (919905812258328785813166173700000000000000)
      linear := (-17289700428636568591478014309785000000000000)
      constant := (76912624746339247340012577904488125949541126) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree019.checked
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
end ForestUnimodality.Stage80KernelData.Cell076.Kernel019

namespace ForestUnimodality.Stage80KernelData.Cell076.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1325718662772208477/625000000000000000)
  centralHi := (212114986043553356321/100000000000000000000)
  directionLo := (54481857925268721573/25000000000000000000)
  directionHi := (217927431701074886293/100000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree020.table
  base := (-42786983435150815192755737900757314017/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6930000000000000000000000000000000000000000
      center := (54054)
      previous := (27027)
      next := (27027)
      square := (715482298423144611188018135100000000000000)
      linear := (-14118927054147171215372996607255000000000000)
      constant := (65947297516819575095282351501321897673277375) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree020.table
  base := (-84186589546798836786623929409012411703/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 8910000000000000000000000000000000000000000
      center := (69498)
      previous := (34749)
      next := (34749)
      square := (919905812258328785813166173700000000000000)
      linear := (-18200314262993298096626401027185000000000000)
      constant := (85222499483718524790066255798080476235048128) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree020.checked
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
end ForestUnimodality.Stage80KernelData.Cell076.Kernel020

namespace ForestUnimodality.Stage80KernelData.Cell076.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54481857925268721573/25000000000000000000)
  centralHi := (217927431701074886293/100000000000000000000)
  directionLo := (55897206812704695447/25000000000000000000)
  directionHi := (223588827250818781789/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree021.table
  base := (-723773992307070343798431986812337771423/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 770000000000000000000000000000000000000000
      center := (6006)
      previous := (3003)
      next := (3003)
      square := (79498033158127179020890903900000000000000)
      linear := (-1647259845804200249228324501245000000000000)
      constant := (8087271774328224687158239282306099932803432) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree021.table
  base := (-5827583911477438753185234411259777284087/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 990000000000000000000000000000000000000000
      center := (7722)
      previous := (3861)
      next := (3861)
      square := (102211756917592087312574019300000000000000)
      linear := (-2123436455261114177974976416065000000000000)
      constant := (10451596509111538797834787832600282048875387) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree021.checked
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
end ForestUnimodality.Stage80KernelData.Cell076.Kernel021

namespace ForestUnimodality.Stage80KernelData.Cell076.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55897206812704695447/25000000000000000000)
  centralHi := (223588827250818781789/100000000000000000000)
  directionLo := (114555185232889292003/50000000000000000000)
  directionHi := (229110370465778584007/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree022.table
  base := (-3074306059081226066222206006746217513907/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (34398)
      previous := (17199)
      next := (17199)
      square := (455306917178364752574193358700000000000000)
      linear := (-9883841017481730263196173718735000000000000)
      constant := (50928256729140258713900522828357336152734026) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree022.table
  base := (-1545970955110286507860499175023786225297/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (6318)
      previous := (3159)
      next := (3159)
      square := (83627801114393525983015106700000000000000)
      linear := (-1820140175609705191538470405635000000000000)
      constant := (9402836681965557978811887316962293263003772) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree022.checked
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
end ForestUnimodality.Stage80KernelData.Cell076.Kernel022

namespace ForestUnimodality.Stage80KernelData.Cell076.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114555185232889292003/50000000000000000000)
  centralHi := (229110370465778584007/100000000000000000000)
  directionLo := (234501940372646238431/100000000000000000000)
  directionHi := (7328185636645194951/3125000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree023.table
  base := (-3215285482750660189705832320717380169993/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 48510000000000000000000000000000000000000000
      center := (378378)
      previous := (189189)
      next := (189189)
      square := (5008376088962012278316126945700000000000000)
      linear := (-113667132098933450088931378233735000000000000)
      constant := (613735535533433575931842647282879977590727914) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree023.table
  base := (-6463783841094669970734062036339242404419/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8910000000000000000000000000000000000000000
      center := (69498)
      previous := (34749)
      next := (34749)
      square := (919905812258328785813166173700000000000000)
      linear := (-20932155766063486612071561179385000000000000)
      constant := (113316818579131686029095985051926735017662671) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree023.checked
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
end ForestUnimodality.Stage80KernelData.Cell076.Kernel023

namespace ForestUnimodality.Stage80KernelData.Cell076.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (234501940372646238431/100000000000000000000)
  centralHi := (7328185636645194951/3125000000000000000)
  directionLo := (239772304952231620333/100000000000000000000)
  directionHi := (119886152476115810167/50000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree024.table
  base := (-6642225502601412081106022303193854672053/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5390000000000000000000000000000000000000000
      center := (42042)
      previous := (21021)
      next := (21021)
      square := (556486232106890253146236327300000000000000)
      linear := (-13179112556174207475856093951265000000000000)
      constant := (74449154289667359002508713904888512331763433) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree024.table
  base := (-3336723227616213612867407845425840135867/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 990000000000000000000000000000000000000000
      center := (7722)
      previous := (3861)
      next := (3861)
      square := (102211756917592087312574019300000000000000)
      linear := (-2426974400046690679691105321865000000000000)
      constant := (13746191449250740969743864212565683653098334) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree024.checked
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
end ForestUnimodality.Stage80KernelData.Cell076.Kernel024

namespace ForestUnimodality.Stage80KernelData.Cell076.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (239772304952231620333/100000000000000000000)
  centralHi := (119886152476115810167/50000000000000000000)
  directionLo := (244929288582798484759/100000000000000000000)
  directionHi := (6123232214569962119/2500000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree025.table
  base := (-3394535558337940707909078323049150433811/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 48510000000000000000000000000000000000000000
      center := (378378)
      previous := (189189)
      next := (189189)
      square := (5008376088962012278316126945700000000000000)
      linear := (-123556893912202284476478312889035000000000000)
      constant := (729104725117889800206225036534089642491165678) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree025.table
  base := (-6818372087329623467245880624776106835419/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (6318)
      previous := (3159)
      next := (3159)
      square := (83627801114393525983015106700000000000000)
      linear := (-2068489403161540511124394055835000000000000)
      constant := (12238456001435334328185717546518135346331061) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree025.checked
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
end ForestUnimodality.Stage80KernelData.Cell076.Kernel025

namespace ForestUnimodality.Stage80KernelData.Cell076.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244929288582798484759/100000000000000000000)
  centralHi := (6123232214569962119/2500000000000000000)
  directionLo := (12498995418557205427/5000000000000000000)
  directionHi := (249979908371144108541/100000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree026.table
  base := (-6876030380072805867726566472184425921581/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (34398)
      previous := (17199)
      next := (17199)
      square := (455306917178364752574193358700000000000000)
      linear := (-11681979528985154697295616383335000000000000)
      constant := (71899878697056705418821143978589168168582779) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree026.table
  base := (-6903487450042331265337491165006785318597/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8910000000000000000000000000000000000000000
      center := (69498)
      previous := (34749)
      next := (34749)
      square := (919905812258328785813166173700000000000000)
      linear := (-23663997269133675127516721331585000000000000)
      constant := (146034307795751152016207751562488954281130073) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree026.checked
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
end ForestUnimodality.Stage80KernelData.Cell076.Kernel026

namespace ForestUnimodality.Stage80KernelData.Cell076.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12498995418557205427/5000000000000000000)
  centralHi := (249979908371144108541/100000000000000000000)
  directionLo := (50986097231624006123/20000000000000000000)
  directionHi := (31866310769765003827/12500000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree027.table
  base := (-1381504564500727572453925862053576969543/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 770000000000000000000000000000000000000000
      center := (6006)
      previous := (3003)
      next := (3003)
      square := (79498033158127179020890903900000000000000)
      linear := (-2118200884531287601016273770545000000000000)
      constant := (13577821763771077039828563451474372866725945) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree027.table
  base := (-6933215140844886695695161861576216470963/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 110000000000000000000000000000000000000000
      center := (858)
      previous := (429)
      next := (429)
      square := (11356861879732454145841557700000000000000)
      linear := (-303390260536918575711914914185000000000000)
      constant := (1949946393194993314848809383967661618819407) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree027.checked
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
end ForestUnimodality.Stage80KernelData.Cell076.Kernel027

namespace ForestUnimodality.Stage80KernelData.Cell076.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (50986097231624006123/20000000000000000000)
  centralHi := (31866310769765003827/12500000000000000000)
  directionLo := (64946685325535115363/25000000000000000000)
  directionHi := (259786741302140461453/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree028.table
  base := (-1377504407038615242044122685834454803351/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6930000000000000000000000000000000000000000
      center := (54054)
      previous := (27027)
      next := (27027)
      square := (715482298423144611188018135100000000000000)
      linear := (-19770219518872219436828387838855000000000000)
      constant := (131799680796674438283094950456748614106388785) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree028.table
  base := (-1727882683944731573870528969927051808113/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8910000000000000000000000000000000000000000
      center := (69498)
      previous := (34749)
      next := (34749)
      square := (919905812258328785813166173700000000000000)
      linear := (-25485224937847134137813494766385000000000000)
      constant := (170353523936665498915067886788159987355885268) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree028.checked
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
end ForestUnimodality.Stage80KernelData.Cell076.Kernel028

namespace ForestUnimodality.Stage80KernelData.Cell076.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64946685325535115363/25000000000000000000)
  centralHi := (259786741302140461453/100000000000000000000)
  directionLo := (132276934062552149927/50000000000000000000)
  directionHi := (52910773625020859971/20000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree029.table
  base := (-2727841554506203541185519049149400549/4000000000000000000000000000000000000)
  polynomial :=
    { denominator := 48510000000000000000000000000000000000000000
      center := (378378)
      previous := (189189)
      next := (189189)
      square := (5008376088962012278316126945700000000000000)
      linear := (-143336417538739953251572182199635000000000000)
      constant := (992466302508781997120772914597968144842002500) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree029.table
  base := (-6842011080301300994695113063144303244187/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8910000000000000000000000000000000000000000
      center := (69498)
      previous := (34749)
      next := (34749)
      square := (919905812258328785813166173700000000000000)
      linear := (-26395838772203863642961881483785000000000000)
      constant := (183254719090062219074523618602053425809429383) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree029.checked
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
end ForestUnimodality.Stage80KernelData.Cell076.Kernel029

namespace ForestUnimodality.Stage80KernelData.Cell076.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132276934062552149927/50000000000000000000)
  centralHi := (52910773625020859971/20000000000000000000)
  directionLo := (16827287563137415663/6250000000000000000)
  directionHi := (269236601010198650609/100000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree030.table
  base := (-1676747036644651319331208872490172174713/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5390000000000000000000000000000000000000000
      center := (42042)
      previous := (21021)
      next := (21021)
      square := (556486232106890253146236327300000000000000)
      linear := (-16475699827263818938371738836365000000000000)
      constant := (118332529200592231805103670670923688791318772) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree030.table
  base := (-6727876030228032217450986339182348586349/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 990000000000000000000000000000000000000000
      center := (7722)
      previous := (3861)
      next := (3861)
      square := (102211756917592087312574019300000000000000)
      linear := (-3034050289617843683123363133465000000000000)
      constant := (21849597157494727099136961933870947489951449) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree030.checked
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
end ForestUnimodality.Stage80KernelData.Cell076.Kernel030

namespace ForestUnimodality.Stage80KernelData.Cell076.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16827287563137415663/6250000000000000000)
  centralHi := (269236601010198650609/100000000000000000000)
  directionLo := (136919634737950134899/50000000000000000000)
  directionHi := (273839269475900269799/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree031.table
  base := (-6552574976145045744713733959477558348319/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 48510000000000000000000000000000000000000000
      center := (378378)
      previous := (189189)
      next := (189189)
      square := (5008376088962012278316126945700000000000000)
      linear := (-153226179352008787639119116854935000000000000)
      constant := (1140163077790143823409045073905484364452304531) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree031.table
  base := (-3286012533320559163350808193083811303321/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8910000000000000000000000000000000000000000
      center := (69498)
      previous := (34749)
      next := (34749)
      square := (919905812258328785813166173700000000000000)
      linear := (-28217066440917322653258654918585000000000000)
      constant := (210525906481192412826804877512109648257481978) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree031.checked
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
end ForestUnimodality.Stage80KernelData.Cell076.Kernel031

namespace ForestUnimodality.Stage80KernelData.Cell076.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (136919634737950134899/50000000000000000000)
  centralHi := (273839269475900269799/100000000000000000000)
  directionLo := (139182922525237044073/50000000000000000000)
  directionHi := (278365845050474088147/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree032.table
  base := (-3179488614205583953111449611959096048439/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 48510000000000000000000000000000000000000000
      center := (378378)
      previous := (189189)
      next := (189189)
      square := (5008376088962012278316126945700000000000000)
      linear := (-158171060258643204832892584182585000000000000)
      constant := (1217964572511155024664659765759692850138044822) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree032.table
  base := (-6377069727629987657501350123089461125363/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8910000000000000000000000000000000000000000
      center := (69498)
      previous := (34749)
      next := (34749)
      square := (919905812258328785813166173700000000000000)
      linear := (-29127680275274052158407041635985000000000000)
      constant := (224890988400844145231706855819047290137301567) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree032.checked
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
end ForestUnimodality.Stage80KernelData.Cell076.Kernel032

namespace ForestUnimodality.Stage80KernelData.Cell076.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (139182922525237044073/50000000000000000000)
  centralHi := (278365845050474088147/100000000000000000000)
  directionLo := (282819981391404475093/100000000000000000000)
  directionHi := (141409990695702237547/50000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree033.table
  base := (-1532137309623123380210755714574420854273/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (3822)
      previous := (1911)
      next := (1911)
      square := (50589657464262750286021484300000000000000)
      linear := (-1647635769346238606329960116265000000000000)
      constant := (13115008344330487817776901684550913512562492) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree033.table
  base := (-6145362515556544036444366210166095015659/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (702)
      previous := (351)
      next := (351)
      square := (9291977901599280664779456300000000000000)
      linear := (-303417112218492744076317458115000000000000)
      constant := (2421611354513164492903466455953505144859069) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree033.checked
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
end ForestUnimodality.Stage80KernelData.Cell076.Kernel033

namespace ForestUnimodality.Stage80KernelData.Cell076.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (282819981391404475093/100000000000000000000)
  centralHi := (141409990695702237547/50000000000000000000)
  directionLo := (143602524401387350529/50000000000000000000)
  directionHi := (287205048802774701059/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree034.table
  base := (-1172682517013689605164268123919319597351/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6930000000000000000000000000000000000000000
      center := (54054)
      previous := (27027)
      next := (27027)
      square := (715482298423144611188018135100000000000000)
      linear := (-24008688867416005602919931262555000000000000)
      constant := (197345220963522819785531319468702057595178785) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree034.table
  base := (-5879022766177516836150297588453862237037/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8910000000000000000000000000000000000000000
      center := (69498)
      previous := (34749)
      next := (34749)
      square := (919905812258328785813166173700000000000000)
      linear := (-30948907943987511168703815070785000000000000)
      constant := (255069625240910585653009754522677608746800033) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree034.checked
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
end ForestUnimodality.Stage80KernelData.Cell076.Kernel034

namespace ForestUnimodality.Stage80KernelData.Cell076.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (143602524401387350529/50000000000000000000)
  centralHi := (287205048802774701059/100000000000000000000)
  directionLo := (145762082038997732889/50000000000000000000)
  directionHi := (291524164077995465779/100000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree035.table
  base := (-2782739602513949982133777395035832976881/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6930000000000000000000000000000000000000000
      center := (54054)
      previous := (27027)
      next := (27027)
      square := (715482298423144611188018135100000000000000)
      linear := (-24715100425506636630601855166505000000000000)
      constant := (209578208524733065282636072645655335494042934) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree035.table
  base := (-5579959857632726709487249350645427460573/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8910000000000000000000000000000000000000000
      center := (69498)
      previous := (34749)
      next := (34749)
      square := (919905812258328785813166173700000000000000)
      linear := (-31859521778344240673852201788185000000000000)
      constant := (270879590577243467596701100331299924132629457) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree035.checked
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
end ForestUnimodality.Stage80KernelData.Cell076.Kernel035

namespace ForestUnimodality.Stage80KernelData.Cell076.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (145762082038997732889/50000000000000000000)
  centralHi := (291524164077995465779/100000000000000000000)
  directionLo := (295780216419124026061/100000000000000000000)
  directionHi := (147890108209562013031/50000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree036.table
  base := (-5236472167476188788588352521093637303007/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5390000000000000000000000000000000000000000
      center := (42042)
      previous := (21021)
      next := (21021)
      square := (556486232106890253146236327300000000000000)
      linear := (-19772287098353430400887383721465000000000000)
      constant := (172807800696211494190609804901695529493679227) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree036.table
  base := (-5249894066073589903304971777233654394997/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (78)
      previous := (39)
      next := (39)
      square := (1032441989066586740531050700000000000000)
      linear := (-36779052315040370571268898435000000000000)
      constant := (322298414522728416108388427682766345605003) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree036.checked
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
end ForestUnimodality.Stage80KernelData.Cell076.Kernel036

namespace ForestUnimodality.Stage80KernelData.Cell076.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (295780216419124026061/100000000000000000000)
  centralHi := (147890108209562013031/50000000000000000000)
  directionLo := (37496986255671616281/12500000000000000000)
  directionHi := (299975890045372930249/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree037.table
  base := (-975588872740090141932182131126773599301/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (34398)
      previous := (17199)
      next := (17199)
      square := (455306917178364752574193358700000000000000)
      linear := (-16626860435619571891069083710985000000000000)
      constant := (149643386677031073904623750745697964213541295) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree037.table
  base := (-4890375325331521301483883555492869709929/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8910000000000000000000000000000000000000000
      center := (69498)
      previous := (34749)
      next := (34749)
      square := (919905812258328785813166173700000000000000)
      linear := (-33680749447057699684148975222985000000000000)
      constant := (303933134537389448459091267674450853088453261) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree037.checked
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
end ForestUnimodality.Stage80KernelData.Cell076.Kernel037

namespace ForestUnimodality.Stage80KernelData.Cell076.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37496986255671616281/12500000000000000000)
  centralHi := (299975890045372930249/100000000000000000000)
  directionLo := (304113683993475529437/100000000000000000000)
  directionHi := (152056841996737764719/50000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree038.table
  base := (-112282383330828094944852454797413706919/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 48510000000000000000000000000000000000000000
      center := (378378)
      previous := (189189)
      next := (189189)
      square := (5008376088962012278316126945700000000000000)
      linear := (-187840345698449707995533388148485000000000000)
      constant := (1739461812051174695605503227271552344309437240) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree038.table
  base := (-900560022371656080690029307426443839979/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8910000000000000000000000000000000000000000
      center := (69498)
      previous := (34749)
      next := (34749)
      square := (919905812258328785813166173700000000000000)
      linear := (-34591363281414429189297361940385000000000000)
      constant := (321174087909640239002263925948745192692893555) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree038.checked
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
end ForestUnimodality.Stage80KernelData.Cell076.Kernel038

namespace ForestUnimodality.Stage80KernelData.Cell076.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (304113683993475529437/100000000000000000000)
  centralHi := (152056841996737764719/50000000000000000000)
  directionLo := (154097964762398239969/50000000000000000000)
  directionHi := (308195929524796479939/100000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree039.table
  base := (-163111456725990579661280554103670749643/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5390000000000000000000000000000000000000000
      center := (42042)
      previous := (21021)
      next := (21021)
      square := (556486232106890253146236327300000000000000)
      linear := (-21420580733898236132145206164015000000000000)
      constant := (203935307034110396821781858713113036648560575) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree039.table
  base := (-2044213324129356657610995355719095669421/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 990000000000000000000000000000000000000000
      center := (7722)
      previous := (3861)
      next := (3861)
      square := (102211756917592087312574019300000000000000)
      linear := (-3944664123974573188271749850865000000000000)
      constant := (37654402931129163611292202329752619057454642) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree039.checked
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
end ForestUnimodality.Stage80KernelData.Cell076.Kernel039

namespace ForestUnimodality.Stage80KernelData.Cell076.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (154097964762398239969/50000000000000000000)
  centralHi := (308195929524796479939/100000000000000000000)
  directionLo := (312224805483521989159/100000000000000000000)
  directionHi := (7805620137088049729/2500000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree040.table
  base := (-3638554415232804799286352639410411567893/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 48510000000000000000000000000000000000000000
      center := (378378)
      previous := (189189)
      next := (189189)
      square := (5008376088962012278316126945700000000000000)
      linear := (-197730107511718542383080322803785000000000000)
      constant := (1933939592613606862649656629188870093484151057) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree040.table
  base := (-729677719243334669265447145438913140381/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8910000000000000000000000000000000000000000
      center := (69498)
      previous := (34749)
      next := (34749)
      square := (919905812258328785813166173700000000000000)
      linear := (-36412590950127888199594135375185000000000000)
      constant := (357078739856395835658399665424469641959602645) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree040.checked
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
end ForestUnimodality.Stage80KernelData.Cell076.Kernel040

namespace ForestUnimodality.Stage80KernelData.Cell076.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (312224805483521989159/100000000000000000000)
  centralHi := (7805620137088049729/2500000000000000000)
  directionLo := (39525293986650372653/12500000000000000000)
  directionHi := (12648094075728119249/4000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree041.table
  base := (-317462387689131099073254242344712871207/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6930000000000000000000000000000000000000000
      center := (54054)
      previous := (27027)
      next := (27027)
      square := (715482298423144611188018135100000000000000)
      linear := (-28953569774050422796693398590205000000000000)
      constant := (290717475695325455556023918425918639802535490) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree041.table
  base := (-1591853695401570057134208241136675482929/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8910000000000000000000000000000000000000000
      center := (69498)
      previous := (34749)
      next := (34749)
      square := (919905812258328785813166173700000000000000)
      linear := (-37323204784484617704742522092585000000000000)
      constant := (375740518239692085633378700724829444289420522) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree041.checked
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
end ForestUnimodality.Stage80KernelData.Cell076.Kernel041

namespace ForestUnimodality.Stage80KernelData.Cell076.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39525293986650372653/12500000000000000000)
  centralHi := (12648094075728119249/4000000000000000000)
  directionLo := (320130482032503101559/100000000000000000000)
  directionHi := (8003262050812577539/2500000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree042.table
  base := (-335864774463053600245468156048510621169/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 770000000000000000000000000000000000000000
      center := (6006)
      previous := (3003)
      next := (3003)
      square := (79498033158127179020890903900000000000000)
      linear := (-3295553481349005980486146943795000000000000)
      constant := (33947007868104858954885415852726617457359896) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree042.table
  base := (-2695303352037987265539244404294218076483/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 990000000000000000000000000000000000000000
      center := (7722)
      previous := (3861)
      next := (3861)
      square := (102211756917592087312574019300000000000000)
      linear := (-4248202068760149689987878756665000000000000)
      constant := (43874904613879279445282336665204872410428183) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree042.checked
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
end ForestUnimodality.Stage80KernelData.Cell076.Kernel042

namespace ForestUnimodality.Stage80KernelData.Cell076.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (320130482032503101559/100000000000000000000)
  centralHi := (8003262050812577539/2500000000000000000)
  directionLo := (8100274829825706881/2500000000000000000)
  directionHi := (324010993193028275241/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree043.table
  base := (-17410156748045905945512281827524664143/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 48510000000000000000000000000000000000000000
      center := (378378)
      previous := (189189)
      next := (189189)
      square := (5008376088962012278316126945700000000000000)
      linear := (-212564750231621793964400724786735000000000000)
      constant := (2244853052975475941816973719881889731780288375) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree043.table
  base := (-136500355970192557017495452202101596187/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8910000000000000000000000000000000000000000
      center := (69498)
      previous := (34749)
      next := (34749)
      square := (919905812258328785813166173700000000000000)
      linear := (-39144432453198076715039295527385000000000000)
      constant := (414478870880958861074969728112411839644758128) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree043.checked
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
end ForestUnimodality.Stage80KernelData.Cell076.Kernel043

namespace ForestUnimodality.Stage80KernelData.Cell076.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8100274829825706881/2500000000000000000)
  centralHi := (324010993193028275241/100000000000000000000)
  directionLo := (327845576290884912539/100000000000000000000)
  directionHi := (16392278814544245627/5000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree044.table
  base := (-821714061814540982817090003477885116493/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (34398)
      previous := (17199)
      next := (17199)
      square := (455306917178364752574193358700000000000000)
      linear := (-19773602830750564650743108374035000000000000)
      constant := (213963033019378654651695344874897505327253174) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree044.table
  base := (-825280775782752605008488958658103040981/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (6318)
      previous := (3159)
      next := (3159)
      square := (83627801114393525983015106700000000000000)
      linear := (-3641367844323164201835243840435000000000000)
      constant := (39504912783156773804826424733637387307361078) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree044.checked
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
end ForestUnimodality.Stage80KernelData.Cell076.Kernel044

namespace ForestUnimodality.Stage80KernelData.Cell076.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (327845576290884912539/100000000000000000000)
  centralHi := (16392278814544245627/5000000000000000000)
  directionLo := (66327164895560631421/20000000000000000000)
  directionHi := (165817912238901578553/50000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree045.table
  base := (-108906978400986210861755350534737785707/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5390000000000000000000000000000000000000000
      center := (42042)
      previous := (21021)
      next := (21021)
      square := (556486232106890253146236327300000000000000)
      linear := (-24717168004987847594660851049115000000000000)
      constant := (273875460793076584048330332006105263335039270) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree045.table
  base := (-1095644091186720439326478408539163153171/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 110000000000000000000000000000000000000000
      center := (858)
      previous := (429)
      next := (429)
      square := (11356861879732454145841557700000000000000)
      linear := (-505748890393969576856000851385000000000000)
      constant := (5618506801615189459653216948581069205315119) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree045.checked
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
end ForestUnimodality.Stage80KernelData.Cell076.Kernel045

namespace ForestUnimodality.Stage80KernelData.Cell076.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66327164895560631421/20000000000000000000)
  centralHi := (165817912238901578553/50000000000000000000)
  directionLo := (335383240876228172683/100000000000000000000)
  directionHi := (83845810219057043171/25000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree046.table
  base := (-513803829076108657188918478732999953291/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 48510000000000000000000000000000000000000000
      center := (378378)
      previous := (189189)
      next := (189189)
      square := (5008376088962012278316126945700000000000000)
      linear := (-227399392951525045545721126769685000000000000)
      constant := (2578707449255817734158469904050038717226585359) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree046.table
  base := (-519859847565315513883208188290101823979/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8910000000000000000000000000000000000000000
      center := (69498)
      previous := (34749)
      next := (34749)
      square := (919905812258328785813166173700000000000000)
      linear := (-41876273956268265230484455679585000000000000)
      constant := (476113361408214241489345201891443519274834711) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree046.checked
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
end ForestUnimodality.Stage80KernelData.Cell076.Kernel046

namespace ForestUnimodality.Stage80KernelData.Cell076.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (335383240876228172683/100000000000000000000)
  centralHi := (83845810219057043171/25000000000000000000)
  directionLo := (169544622772451789729/50000000000000000000)
  directionHi := (339089245544903579459/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree047.table
  base := (81820640382743727732483431404443627721/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 48510000000000000000000000000000000000000000
      center := (378378)
      previous := (189189)
      next := (189189)
      square := (5008376088962012278316126945700000000000000)
      linear := (-232344273858159462739494594097335000000000000)
      constant := (2695075605879621086799020300406312956038074571) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree047.table
  base := (76244687365102414057496202518470382621/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (6318)
      previous := (3159)
      next := (3159)
      square := (83627801114393525983015106700000000000000)
      linear := (-3889717071874999521421167490635000000000000)
      constant := (45236044102051213968430459489198996100992301) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree047.checked
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
end ForestUnimodality.Stage80KernelData.Cell076.Kernel047

namespace ForestUnimodality.Stage80KernelData.Cell076.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (169544622772451789729/50000000000000000000)
  centralHi := (339089245544903579459/100000000000000000000)
  directionLo := (85688795441623279429/25000000000000000000)
  directionHi := (342755181766493117717/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree048.table
  base := (69730873803616789128215523847530688131/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (78)
      previous := (39)
      next := (39)
      square := (1032441989066586740531050700000000000000)
      linear := (-48915513247741471847715535235000000000000)
      constant := (580082707960319506726113482218475306881310) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree048.table
  base := (173044279841795872458414482991010039351/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 990000000000000000000000000000000000000000
      center := (7722)
      previous := (3861)
      next := (3861)
      square := (102211756917592087312574019300000000000000)
      linear := (-4855277958331302693420136568265000000000000)
      constant := (57727553705623578222397367660784439975582996) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree048.checked
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
end ForestUnimodality.Stage80KernelData.Cell076.Kernel048

namespace ForestUnimodality.Stage80KernelData.Cell076.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (85688795441623279429/25000000000000000000)
  centralHi := (342755181766493117717/100000000000000000000)
  directionLo := (21648895108511705121/6250000000000000000)
  directionHi := (346382321736187281937/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree049.table
  base := (333053609813025589803836494167732422669/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 990000000000000000000000000000000000000000
      center := (7722)
      previous := (3861)
      next := (3861)
      square := (102211756917592087312574019300000000000000)
      linear := (-4943551748396495859735541403115000000000000)
      constant := (59906573814244778059897494339212922039376924) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree049.table
  base := (331873449182716376252320189157876775983/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8910000000000000000000000000000000000000000
      center := (69498)
      previous := (34749)
      next := (34749)
      square := (919905812258328785813166173700000000000000)
      linear := (-44608115459338453745929615831785000000000000)
      constant := (541967460798687127108152492936173672829603412) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree049.checked
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
end ForestUnimodality.Stage80KernelData.Cell076.Kernel049

namespace ForestUnimodality.Stage80KernelData.Cell076.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21648895108511705121/6250000000000000000)
  centralHi := (346382321736187281937/100000000000000000000)
  directionLo := (87492967929900437989/25000000000000000000)
  directionHi := (349971871719601751957/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree050.table
  base := (496533939210733972966346527566732908267/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 48510000000000000000000000000000000000000000
      center := (378378)
      previous := (189189)
      next := (189189)
      square := (5008376088962012278316126945700000000000000)
      linear := (-247178916578062714320814996080285000000000000)
      constant := (3059396357587226578095199447627342385352012868) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree050.table
  base := (396358997045433087156134596096942715141/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8910000000000000000000000000000000000000000
      center := (69498)
      previous := (34749)
      next := (34749)
      square := (919905812258328785813166173700000000000000)
      linear := (-45518729293695183251078002549185000000000000)
      constant := (564854561303590099098254517047361879795953155) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree050.checked
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
end ForestUnimodality.Stage80KernelData.Cell076.Kernel050

namespace ForestUnimodality.Stage80KernelData.Cell076.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (87492967929900437989/25000000000000000000)
  centralHi := (349971871719601751957/100000000000000000000)
  directionLo := (176762488369627796933/50000000000000000000)
  directionHi := (353524976739255593867/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree051.table
  base := (1329355196564712496150271556253776684887/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5390000000000000000000000000000000000000000
      center := (42042)
      previous := (21021)
      next := (21021)
      square := (556486232106890253146236327300000000000000)
      linear := (-28013755276077459057176495934215000000000000)
      constant := (353989131208573919600603038085806571266308186) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree051.table
  base := (663680130175159286104946626862968660507/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 990000000000000000000000000000000000000000
      center := (7722)
      previous := (3861)
      next := (3861)
      square := (102211756917592087312574019300000000000000)
      linear := (-5158815903116879195136265474065000000000000)
      constant := (65356551551006513051462965603002735589560772) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree051.checked
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
end ForestUnimodality.Stage80KernelData.Cell076.Kernel051

namespace ForestUnimodality.Stage80KernelData.Cell076.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (176762488369627796933/50000000000000000000)
  centralHi := (353524976739255593867/100000000000000000000)
  directionLo := (178521362420622530437/50000000000000000000)
  directionHi := (2856341798729960487/800000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree052.table
  base := (334961182129035134589837956561133078077/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 48510000000000000000000000000000000000000000
      center := (378378)
      previous := (189189)
      next := (189189)
      square := (5008376088962012278316126945700000000000000)
      linear := (-257068678391331548708361930735585000000000000)
      constant := (3314938002786200489821427464142525565617515270) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree052.table
  base := (133837835680606608431583518253993125453/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8910000000000000000000000000000000000000000
      center := (69498)
      previous := (34749)
      next := (34749)
      square := (919905812258328785813166173700000000000000)
      linear := (-47339956962408642261374775983985000000000000)
      constant := (612030379625670403363546916332527696869465575) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree052.checked
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
end ForestUnimodality.Stage80KernelData.Cell076.Kernel052

namespace ForestUnimodality.Stage80KernelData.Cell076.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (178521362420622530437/50000000000000000000)
  centralHi := (2856341798729960487/800000000000000000)
  directionLo := (360526150987179925893/100000000000000000000)
  directionHi := (180263075493589962947/50000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree053.table
  base := (4058545753611328228668133835095867507503/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 48510000000000000000000000000000000000000000
      center := (378378)
      previous := (189189)
      next := (189189)
      square := (5008376088962012278316126945700000000000000)
      linear := (-262013559297965965902135398063235000000000000)
      constant := (3446502395724629728345120627049267553278897053) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree053.table
  base := (4055178711750401573417612013550843387967/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8910000000000000000000000000000000000000000
      center := (69498)
      previous := (34749)
      next := (34749)
      square := (919905812258328785813166173700000000000000)
      linear := (-48250570796765371766523162701385000000000000)
      constant := (636318547786233926676623228169428801458678597) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree053.checked
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
end ForestUnimodality.Stage80KernelData.Cell076.Kernel053

namespace ForestUnimodality.Stage80KernelData.Cell076.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (360526150987179925893/100000000000000000000)
  centralHi := (180263075493589962947/50000000000000000000)
  directionLo := (181988120305420403853/50000000000000000000)
  directionHi := (363976240610840807707/100000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree054.table
  base := (299077934902012132769519167818452361857/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5390000000000000000000000000000000000000000
      center := (42042)
      previous := (21021)
      next := (21021)
      square := (556486232106890253146236327300000000000000)
      linear := (-29662048911622264788434318376765000000000000)
      constant := (397843785894852172051216406966588833168654768) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree054.table
  base := (4782155536264412010315942185593256854827/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 110000000000000000000000000000000000000000
      center := (858)
      previous := (429)
      next := (429)
      square := (11356861879732454145841557700000000000000)
      linear := (-606928205322495077428043819985000000000000)
      constant := (8161397947067459555686473979531525825403097) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree054.checked
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
end ForestUnimodality.Stage80KernelData.Cell076.Kernel054

namespace ForestUnimodality.Stage80KernelData.Cell076.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (181988120305420403853/50000000000000000000)
  centralHi := (363976240610840807707/100000000000000000000)
  directionLo := (367393932874197727139/100000000000000000000)
  directionHi := (18369696643709886357/5000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree055.table
  base := (5529476391364659602923861286020160394609/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (4914)
      previous := (2457)
      next := (2457)
      square := (65043845311194964653456194100000000000000)
      linear := (-3531211962483568834930939385955000000000000)
      constant := (48275478898298602053823760200419270104860367) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree055.table
  base := (172707468766822624219128392030974577327/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (6318)
      previous := (3159)
      next := (3159)
      square := (83627801114393525983015106700000000000000)
      linear := (-4551981678679893706983630557835000000000000)
      constant := (62390384173829952720598494376819286104431584) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree055.checked
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
end ForestUnimodality.Stage80KernelData.Cell076.Kernel055

namespace ForestUnimodality.Stage80KernelData.Cell076.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (367393932874197727139/100000000000000000000)
  centralHi := (18369696643709886357/5000000000000000000)
  directionLo := (370780123653278277473/100000000000000000000)
  directionHi := (185390061826639138737/50000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree056.table
  base := (3145509304875689588808389404968374479349/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6930000000000000000000000000000000000000000
      center := (54054)
      previous := (27027)
      next := (27027)
      square := (715482298423144611188018135100000000000000)
      linear := (-39549743145409888211922257149455000000000000)
      constant := (550907822422609624919811738273416167028377714) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree056.table
  base := (3144207618321273224434447054513197870757/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8910000000000000000000000000000000000000000
      center := (69498)
      previous := (34749)
      next := (34749)
      square := (919905812258328785813166173700000000000000)
      linear := (-50982412299835560281968322853585000000000000)
      constant := (711981333828904428826954605246702518605688974) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree056.checked
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
end ForestUnimodality.Stage80KernelData.Cell076.Kernel056

namespace ForestUnimodality.Stage80KernelData.Cell076.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (370780123653278277473/100000000000000000000)
  centralHi := (185390061826639138737/50000000000000000000)
  directionLo := (23383479267549109491/6250000000000000000)
  directionHi := (374135668280785751857/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree057.table
  base := (441854965150083059304279869846643440737/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5390000000000000000000000000000000000000000
      center := (42042)
      previous := (21021)
      next := (21021)
      square := (556486232106890253146236327300000000000000)
      linear := (-31310342547167070519692140819315000000000000)
      constant := (444224641833005215600791279785249953032915888) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree057.table
  base := (7067291547748848000353135108899917756109/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 990000000000000000000000000000000000000000
      center := (7722)
      previous := (3861)
      next := (3861)
      square := (102211756917592087312574019300000000000000)
      linear := (-5765891792688032198568523285665000000000000)
      constant := (82014931752212790722913538303236091857854791) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree057.checked
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
end ForestUnimodality.Stage80KernelData.Cell076.Kernel057

namespace ForestUnimodality.Stage80KernelData.Cell076.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23383479267549109491/6250000000000000000)
  centralHi := (374135668280785751857/100000000000000000000)
  directionLo := (188730692034629053551/50000000000000000000)
  directionHi := (377461384069258107103/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree058.table
  base := (7865283889397507962200108716528046386039/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 48510000000000000000000000000000000000000000
      center := (378378)
      previous := (189189)
      next := (189189)
      square := (5008376088962012278316126945700000000000000)
      linear := (-286737963831138051871002734701485000000000000)
      constant := (4142212084860733684419570685064645053018675189) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree058.table
  base := (7863094312391860754624816993003442298591/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (6318)
      previous := (3159)
      next := (3159)
      square := (83627801114393525983015106700000000000000)
      linear := (-4800330906231729026569554208035000000000000)
      constant := (69523020639857809107991154875163278826185871) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree058.checked
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
end ForestUnimodality.Stage80KernelData.Cell076.Kernel058

namespace ForestUnimodality.Stage80KernelData.Cell076.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (188730692034629053551/50000000000000000000)
  centralHi := (377461384069258107103/100000000000000000000)
  directionLo := (380758052635856674797/100000000000000000000)
  directionHi := (190379026317928337399/50000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree059.table
  base := (1735534845852291885450636161442654950319/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (34398)
      previous := (17199)
      next := (17199)
      square := (455306917178364752574193358700000000000000)
      linear := (-26516622248888406278616018366285000000000000)
      constant := (389902265176585055689636421088846054165453395) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree059.table
  base := (4337833548093848484576485095848401671511/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8910000000000000000000000000000000000000000
      center := (69498)
      previous := (34749)
      next := (34749)
      square := (919905812258328785813166173700000000000000)
      linear := (-53714253802905748797413483005785000000000000)
      constant := (791837718251430735893402088053166851778632602) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree059.checked
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
end ForestUnimodality.Stage80KernelData.Cell076.Kernel059

namespace ForestUnimodality.Stage80KernelData.Cell076.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (380758052635856674797/100000000000000000000)
  centralHi := (190379026317928337399/50000000000000000000)
  directionLo := (76805284409503914361/20000000000000000000)
  directionHi := (192013211023759785903/50000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree060.table
  base := (950670831300186941322262485161861136059/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5390000000000000000000000000000000000000000
      center := (42042)
      previous := (21021)
      next := (21021)
      square := (556486232106890253146236327300000000000000)
      linear := (-32958636182711876250949963261865000000000000)
      constant := (493128842575266206780897329716297431523358010) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree060.table
  base := (9504868950473579945104073862256325433417/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 990000000000000000000000000000000000000000
      center := (7722)
      previous := (3861)
      next := (3861)
      square := (102211756917592087312574019300000000000000)
      linear := (-6069429737473608700284652191465000000000000)
      constant := (91043081535960121064895481215263376217908283) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree060.checked
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
end ForestUnimodality.Stage80KernelData.Cell076.Kernel060

namespace ForestUnimodality.Stage80KernelData.Cell076.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (76805284409503914361/20000000000000000000)
  centralHi := (192013211023759785903/50000000000000000000)
  directionLo := (387267208803158869317/100000000000000000000)
  directionHi := (193633604401579434659/50000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree061.table
  base := (5176129013297908778626459086849504729079/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 48510000000000000000000000000000000000000000
      center := (378378)
      previous := (189189)
      next := (189189)
      square := (5008376088962012278316126945700000000000000)
      linear := (-301572606551041303452323136684435000000000000)
      constant := (4589915462084489243065584550971261394881524458) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree061.table
  base := (10350572879365253147476085806190712519217/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8910000000000000000000000000000000000000000
      center := (69498)
      previous := (34749)
      next := (34749)
      square := (919905812258328785813166173700000000000000)
      linear := (-55535481471619207807710256440585000000000000)
      constant := (847403160601734088687187612680550924854622347) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree061.checked
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
end ForestUnimodality.Stage80KernelData.Cell076.Kernel061

namespace ForestUnimodality.Stage80KernelData.Cell076.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (387267208803158869317/100000000000000000000)
  centralHi := (193633604401579434659/50000000000000000000)
  directionLo := (195240549833890343547/50000000000000000000)
  directionHi := (78096219933556137419/20000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree062.table
  base := (11214207905272996931953368251419295382507/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6930000000000000000000000000000000000000000
      center := (54054)
      previous := (27027)
      next := (27027)
      square := (715482298423144611188018135100000000000000)
      linear := (-43788212493953674378013800573155000000000000)
      constant := (677741713363444999970536304732381071700077351) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree062.table
  base := (5606332229280278148824008138570465343367/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8910000000000000000000000000000000000000000
      center := (69498)
      previous := (34749)
      next := (34749)
      square := (919905812258328785813166173700000000000000)
      linear := (-56446095305975937312858643157985000000000000)
      constant := (875883896633656508394535631418702569241879994) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree062.checked
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
end ForestUnimodality.Stage80KernelData.Cell076.Kernel062

namespace ForestUnimodality.Stage80KernelData.Cell076.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (195240549833890343547/50000000000000000000)
  centralHi := (78096219933556137419/20000000000000000000)
  directionLo := (39366875337182794853/10000000000000000000)
  directionHi := (393668753371827948531/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree063.table
  base := (2418490776923019274637578330447752255987/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 770000000000000000000000000000000000000000
      center := (6006)
      previous := (3003)
      next := (3003)
      square := (79498033158127179020890903900000000000000)
      linear := (-4943847116893811711743969386345000000000000)
      constant := (77793470995869522281831120209232384618554995) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree063.table
  base := (6045520295433934205574988401547951627849/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 110000000000000000000000000000000000000000
      center := (858)
      previous := (429)
      next := (429)
      square := (11356861879732454145841557700000000000000)
      linear := (-708107520251020578000086788585000000000000)
      constant := (11170738889627291535912848352139054935812678) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree063.checked
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
end ForestUnimodality.Stage80KernelData.Cell076.Kernel063

namespace ForestUnimodality.Stage80KernelData.Cell076.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39366875337182794853/10000000000000000000)
  centralHi := (393668753371827948531/100000000000000000000)
  directionLo := (396830802187656449781/100000000000000000000)
  directionHi := (198415401093828224891/50000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree064.table
  base := (6493451087481154313055928560773287087479/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 48510000000000000000000000000000000000000000
      center := (378378)
      previous := (189189)
      next := (189189)
      square := (5008376088962012278316126945700000000000000)
      linear := (-316407249270944555033643538667385000000000000)
      constant := (5060305044697844229957152564920062431322721258) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree064.table
  base := (12985608384925065056540111973503339798641/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8910000000000000000000000000000000000000000
      center := (69498)
      previous := (34749)
      next := (34749)
      square := (919905812258328785813166173700000000000000)
      linear := (-58267322974689396323155416592785000000000000)
      constant := (934240938113992753861988174823431475760589131) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree064.checked
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
end ForestUnimodality.Stage80KernelData.Cell076.Kernel064

namespace ForestUnimodality.Stage80KernelData.Cell076.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (396830802187656449781/100000000000000000000)
  centralHi := (198415401093828224891/50000000000000000000)
  directionLo := (12498995418557205427/3125000000000000000)
  directionHi := (79993570678766114733/20000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree065.table
  base := (555898729878103901427229390229412831543/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 48510000000000000000000000000000000000000000
      center := (378378)
      previous := (189189)
      next := (189189)
      square := (5008376088962012278316126945700000000000000)
      linear := (-321352130177578972227417005995035000000000000)
      constant := (5222140699366372741011009093779534541145377325) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree065.table
  base := (13896284144914392589886043594335768839231/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8910000000000000000000000000000000000000000
      center := (69498)
      previous := (34749)
      next := (34749)
      square := (919905812258328785813166173700000000000000)
      linear := (-59177936809046125828303803310185000000000000)
      constant := (964117086223229308256934257348328170035754821) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree065.checked
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
end ForestUnimodality.Stage80KernelData.Cell076.Kernel065

namespace ForestUnimodality.Stage80KernelData.Cell076.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12498995418557205427/3125000000000000000)
  centralHi := (79993570678766114733/20000000000000000000)
  directionLo := (25192530664802725793/6250000000000000000)
  directionHi := (403080490636843612689/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree066.table
  base := (7412037958610676151342012377864610084177/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (3822)
      previous := (1911)
      next := (1911)
      square := (50589657464262750286021484300000000000000)
      linear := (-3295929404891044337587782558815000000000000)
      constant := (54409043102826906160908687123583231788249346) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree066.table
  base := (14822992460285796533241370209397845870753/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (702)
      previous := (351)
      next := (351)
      square := (9291977901599280664779456300000000000000)
      linear := (-606955057004069245792446363915000000000000)
      constant := (10045032597946668475292209296974580612836777) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree066.checked
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
end ForestUnimodality.Stage80KernelData.Cell076.Kernel066

namespace ForestUnimodality.Stage80KernelData.Cell076.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25192530664802725793/6250000000000000000)
  centralHi := (403080490636843612689/100000000000000000000)
  directionLo := (203084637599455313583/50000000000000000000)
  directionHi := (406169275198910627167/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree067.table
  base := (15766656524372377183247611992032416115343/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 48510000000000000000000000000000000000000000
      center := (378378)
      previous := (189189)
      next := (189189)
      square := (5008376088962012278316126945700000000000000)
      linear := (-331241891990847806614963940650335000000000000)
      constant := (5553368415061884191160472026792494250575528893) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree067.table
  base := (7882832692794441393639796629461865485447/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8910000000000000000000000000000000000000000
      center := (69498)
      previous := (34749)
      next := (34749)
      square := (919905812258328785813166173700000000000000)
      linear := (-60999164477759584838600576744985000000000000)
      constant := (1025264300495069065110471653763146044295066554) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree067.checked
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
end ForestUnimodality.Stage80KernelData.Cell076.Kernel067

namespace ForestUnimodality.Stage80KernelData.Cell076.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (203084637599455313583/50000000000000000000)
  centralHi := (406169275198910627167/100000000000000000000)
  directionLo := (81846949435926619553/20000000000000000000)
  directionHi := (204617373589816548883/50000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree068.table
  base := (836257409315376392896440874072337789057/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 48510000000000000000000000000000000000000000
      center := (378378)
      previous := (189189)
      next := (189189)
      square := (5008376088962012278316126945700000000000000)
      linear := (-336186772897482223808737407977985000000000000)
      constant := (5722759842822376086608928662705303212294310140) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree068.table
  base := (8362120850746833752470784526796309156317/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8910000000000000000000000000000000000000000
      center := (69498)
      previous := (34749)
      next := (34749)
      square := (919905812258328785813166173700000000000000)
      linear := (-61909778312116314343748963462385000000000000)
      constant := (1056535251571852950818833360409131022916556894) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree068.checked
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
end ForestUnimodality.Stage80KernelData.Cell076.Kernel068

namespace ForestUnimodality.Stage80KernelData.Cell076.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (81846949435926619553/20000000000000000000)
  centralHi := (204617373589816548883/50000000000000000000)
  directionLo := (206138713299290317851/50000000000000000000)
  directionHi := (412277426598580635703/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree069.table
  base := (4424873782720567768252710286215981339961/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 770000000000000000000000000000000000000000
      center := (6006)
      previous := (3003)
      next := (3003)
      square := (79498033158127179020890903900000000000000)
      linear := (-5414788155620899063531918655645000000000000)
      constant := (93566179046201051832723011679197022252707988) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree069.table
  base := (1769866624896324176410925252469468626867/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (702)
      previous := (351)
      next := (351)
      square := (9291977901599280664779456300000000000000)
      linear := (-634549415620939836857548991715000000000000)
      constant := (10992636679599696467973804668507252176418030) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree069.checked
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
end ForestUnimodality.Stage80KernelData.Cell076.Kernel069

namespace ForestUnimodality.Stage80KernelData.Cell076.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (206138713299290317851/50000000000000000000)
  centralHi := (412277426598580635703/100000000000000000000)
  directionLo := (415297814425163894353/100000000000000000000)
  directionHi := (207648907212581947177/50000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree070.table
  base := (4672411773161882366481023444919921677517/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (4914)
      previous := (2457)
      next := (2457)
      square := (65043845311194964653456194100000000000000)
      linear := (-4494500450788974781769926527705000000000000)
      constant := (78819434837520276018604028166532320262734284) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree070.table
  base := (1868888932933704322034791758200603652801/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8910000000000000000000000000000000000000000
      center := (69498)
      previous := (34749)
      next := (34749)
      square := (919905812258328785813166173700000000000000)
      linear := (-63731005980829773354045736897185000000000000)
      constant := (1120471595339113502593300218136017378546456910) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree070.checked
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
end ForestUnimodality.Stage80KernelData.Cell076.Kernel070

namespace ForestUnimodality.Stage80KernelData.Cell076.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (415297814425163894353/100000000000000000000)
  centralHi := (207648907212581947177/50000000000000000000)
  directionLo := (83659278708314881619/20000000000000000000)
  directionHi := (13071762298174200253/3125000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree071.table
  base := (19695558769152956461025335042735769999377/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 48510000000000000000000000000000000000000000
      center := (378378)
      previous := (189189)
      next := (189189)
      square := (5008376088962012278316126945700000000000000)
      linear := (-351021415617385475390057809960935000000000000)
      constant := (6246041230795374419283364602901371220266977827) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree071.table
  base := (19694866163800240701944516871819681358741/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8910000000000000000000000000000000000000000
      center := (69498)
      previous := (34749)
      next := (34749)
      square := (919905812258328785813166173700000000000000)
      linear := (-64641619815186502859194123614585000000000000)
      constant := (1153136903850159593036517703078376336090638231) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree071.checked
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
end ForestUnimodality.Stage80KernelData.Cell076.Kernel071

namespace ForestUnimodality.Stage80KernelData.Cell076.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (83659278708314881619/20000000000000000000)
  centralHi := (13071762298174200253/3125000000000000000)
  directionLo := (8425472592880651377/2000000000000000000)
  directionHi := (421273629644032568851/100000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree072.table
  base := (10358594665465498802762278056485611110061/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5390000000000000000000000000000000000000000
      center := (42042)
      previous := (21021)
      next := (21021)
      square := (556486232106890253146236327300000000000000)
      linear := (-39551810724891099175981253032065000000000000)
      constant := (713944814085095406262625411692621488776645758) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree072.table
  base := (5179139101590148696557286934824758137817/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 110000000000000000000000000000000000000000
      center := (858)
      previous := (429)
      next := (429)
      square := (11356861879732454145841557700000000000000)
      linear := (-809286835179546078572129757185000000000000)
      constant := (14645270627965791806585928811652289358063948) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree072.checked
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
end ForestUnimodality.Stage80KernelData.Cell076.Kernel072

namespace ForestUnimodality.Stage80KernelData.Cell076.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8425472592880651377/2000000000000000000)
  centralHi := (421273629644032568851/100000000000000000000)
  directionLo := (1325718662772208477/312500000000000000)
  directionHi := (424229972087106712641/100000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree073.table
  base := (10877250989930851141453143490876891726549/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 48510000000000000000000000000000000000000000
      center := (378378)
      previous := (189189)
      next := (189189)
      square := (5008376088962012278316126945700000000000000)
      linear := (-360911177430654309777604744616235000000000000)
      constant := (6607482591892834084232585930807780103530978398) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree073.table
  base := (2175392370503608165932100840192737355909/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8910000000000000000000000000000000000000000
      center := (69498)
      previous := (34749)
      next := (34749)
      square := (919905812258328785813166173700000000000000)
      linear := (-66462847483899961869490897049385000000000000)
      constant := (1219861613994706149265960015744172289841149190) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree073.checked
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
end ForestUnimodality.Stage80KernelData.Cell076.Kernel073

namespace ForestUnimodality.Stage80KernelData.Cell076.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1325718662772208477/312500000000000000)
  centralHi := (424229972087106712641/100000000000000000000)
  directionLo := (42716585467543770511/10000000000000000000)
  directionHi := (427165854675437705111/100000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree074.table
  base := (22807463551141533057727763110196637946351/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 48510000000000000000000000000000000000000000
      center := (378378)
      previous := (189189)
      next := (189189)
      square := (5008376088962012278316126945700000000000000)
      linear := (-365856058337288726971378211943885000000000000)
      constant := (6791978865293838742790903428845791390677748701) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree074.table
  base := (2850866913310110952807881811800583861409/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8910000000000000000000000000000000000000000
      center := (69498)
      previous := (34749)
      next := (34749)
      square := (919905812258328785813166173700000000000000)
      linear := (-67373461318256691374639283766785000000000000)
      constant := (1253920954055359511828424522549904561764123352) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree074.checked
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
end ForestUnimodality.Stage80KernelData.Cell076.Kernel074

namespace ForestUnimodality.Stage80KernelData.Cell076.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (42716585467543770511/10000000000000000000)
  centralHi := (427165854675437705111/100000000000000000000)
  directionLo := (53760212050852340377/12500000000000000000)
  directionHi := (430081696406818723017/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree075.table
  base := (955041766182041545777052737221308024207/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5390000000000000000000000000000000000000000
      center := (42042)
      previous := (21021)
      next := (21021)
      square := (556486232106890253146236327300000000000000)
      linear := (-41200104360435904907239075474615000000000000)
      constant := (775443555774602008205812967361432125626189325) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree075.table
  base := (9326391288964765477996972851937210743/3906250000000000000000000000000000000)
  polynomial :=
    { denominator := 990000000000000000000000000000000000000000
      center := (7722)
      previous := (3861)
      next := (3861)
      square := (102211756917592087312574019300000000000000)
      linear := (-7587119461401491208865296720465000000000000)
      constant := (143160546083659671021281874390719966690705920) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree075.checked
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
end ForestUnimodality.Stage80KernelData.Cell076.Kernel075

namespace ForestUnimodality.Stage80KernelData.Cell076.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53760212050852340377/12500000000000000000)
  centralHi := (430081696406818723017/100000000000000000000)
  directionLo := (21648895108511705121/5000000000000000000)
  directionHi := (432977902170234102421/100000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree076.table
  base := (24960216851141311546987863307895479606761/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6930000000000000000000000000000000000000000
      center := (54054)
      previous := (27027)
      next := (27027)
      square := (715482298423144611188018135100000000000000)
      linear := (-53677974307222508765560735228455000000000000)
      constant := (1024074553034961561021951630601476567367485373) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree076.table
  base := (4991955259065334175313748187476299781383/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8910000000000000000000000000000000000000000
      center := (69498)
      previous := (34749)
      next := (34749)
      square := (919905812258328785813166173700000000000000)
      linear := (-69194688986970150384936057201585000000000000)
      constant := (1323433472396179844568632605407466915526061265) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree076.checked
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
end ForestUnimodality.Stage80KernelData.Cell076.Kernel076

namespace ForestUnimodality.Stage80KernelData.Cell076.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21648895108511705121/5000000000000000000)
  centralHi := (432977902170234102421/100000000000000000000)
  directionLo := (87170972680429954517/20000000000000000000)
  directionHi := (217927431701074886293/50000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree077.table
  base := (26059957361842240067333612591644367244111/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (4914)
      previous := (2457)
      next := (2457)
      square := (65043845311194964653456194100000000000000)
      linear := (-4944035078664830890294787193855000000000000)
      constant := (95591796822545560920098147609771095136378993) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree077.table
  base := (5211911027185231824189514649552756013887/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (6318)
      previous := (3159)
      next := (3159)
      square := (83627801114393525983015106700000000000000)
      linear := (-6373209347393352717280403992635000000000000)
      constant := (123535145967195153455079010681413866185624235) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree077.checked
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
end ForestUnimodality.Stage80KernelData.Cell076.Kernel077

namespace ForestUnimodality.Stage80KernelData.Cell076.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (87170972680429954517/20000000000000000000)
  centralHi := (217927431701074886293/50000000000000000000)
  directionLo := (438712958704067073523/100000000000000000000)
  directionHi := (109678239676016768381/25000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree078.table
  base := (13587621902420415009336114446420503106587/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5390000000000000000000000000000000000000000
      center := (42042)
      previous := (21021)
      next := (21021)
      square := (556486232106890253146236327300000000000000)
      linear := (-42848397995980710638496897917165000000000000)
      constant := (839459038677397225570431087089473802348900786) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree078.table
  base := (27174876635923489294717518830988298368133/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 990000000000000000000000000000000000000000
      center := (7722)
      previous := (3861)
      next := (3861)
      square := (102211756917592087312574019300000000000000)
      linear := (-7890657406187067710581425626265000000000000)
      constant := (154978255027671766102547013455237841538445167) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree078.checked
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
end ForestUnimodality.Stage80KernelData.Cell076.Kernel078

namespace ForestUnimodality.Stage80KernelData.Cell076.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (438712958704067073523/100000000000000000000)
  centralHi := (109678239676016768381/25000000000000000000)
  directionLo := (3449629331438267919/781250000000000000)
  directionHi := (441552554424098293633/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree079.table
  base := (28306056458889048417989480662151909853257/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 48510000000000000000000000000000000000000000
      center := (378378)
      previous := (189189)
      next := (189189)
      square := (5008376088962012278316126945700000000000000)
      linear := (-390580462870460812940245548582135000000000000)
      constant := (7752210753858657237012026630523188914698149707) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree079.table
  base := (14152860673289170183262747609089698288341/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8910000000000000000000000000000000000000000
      center := (69498)
      previous := (34749)
      next := (34749)
      square := (919905812258328785813166173700000000000000)
      linear := (-71926530490040338900381217353785000000000000)
      constant := (1431186523897049839280859019732462842349823662) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree079.checked
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
end ForestUnimodality.Stage80KernelData.Cell076.Kernel079

namespace ForestUnimodality.Stage80KernelData.Cell076.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3449629331438267919/781250000000000000)
  centralHi := (441552554424098293633/100000000000000000000)
  directionLo := (444374005205093100251/100000000000000000000)
  directionHi := (111093501301273275063/25000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree080.table
  base := (7363094387495273822756560702463337716331/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 48510000000000000000000000000000000000000000
      center := (378378)
      previous := (189189)
      next := (189189)
      square := (5008376088962012278316126945700000000000000)
      linear := (-395525343777095230134019015909785000000000000)
      constant := (7951806486400552675806866890295898605047686724) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree080.table
  base := (14726035872249741931626889607136235964607/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (6318)
      previous := (3159)
      next := (3159)
      square := (83627801114393525983015106700000000000000)
      linear := (-6621558574945188036866327642835000000000000)
      constant := (133457570542710630591829902003156070226266334) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree080.checked
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
end ForestUnimodality.Stage80KernelData.Cell076.Kernel080

namespace ForestUnimodality.Stage80KernelData.Cell076.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (444374005205093100251/100000000000000000000)
  centralHi := (111093501301273275063/25000000000000000000)
  directionLo := (447177654501637563577/100000000000000000000)
  directionHi := (223588827250818781789/50000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree081.table
  base := (30614191059092773835400758589862974879821/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (3822)
      previous := (1911)
      next := (1911)
      square := (50589657464262750286021484300000000000000)
      linear := (-4045153784684137851795883669065000000000000)
      constant := (82362812808221969372020673344930785769111229) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree081.table
  base := (6122782408209912015760014366792047131017/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 110000000000000000000000000000000000000000
      center := (858)
      previous := (429)
      next := (429)
      square := (11356861879732454145841557700000000000000)
      linear := (-910466150108071579144172725785000000000000)
      constant := (18584500461724337026081428143308562592205935) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree081.checked
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
end ForestUnimodality.Stage80KernelData.Cell076.Kernel081

namespace ForestUnimodality.Stage80KernelData.Cell076.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (447177654501637563577/100000000000000000000)
  centralHi := (223588827250818781789/50000000000000000000)
  directionLo := (112490958767014848843/25000000000000000000)
  directionHi := (449963835068059395373/100000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree082.table
  base := (31791482548903437401816645190533788628563/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 48510000000000000000000000000000000000000000
      center := (378378)
      previous := (189189)
      next := (189189)
      square := (5008376088962012278316126945700000000000000)
      linear := (-405415105590364064521565950565085000000000000)
      constant := (8358546628663481656185829190060636908637159113) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree082.table
  base := (1986951750663569745770529921239061917839/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8910000000000000000000000000000000000000000
      center := (69498)
      previous := (34749)
      next := (34749)
      square := (919905812258328785813166173700000000000000)
      linear := (-74658371993110527415826377505985000000000000)
      constant := (1543120295511593122393234510597654066700712784) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree082.checked
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
end ForestUnimodality.Stage80KernelData.Cell076.Kernel082

namespace ForestUnimodality.Stage80KernelData.Cell076.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (112490958767014848843/25000000000000000000)
  centralHi := (449963835068059395373/100000000000000000000)
  directionLo := (452732869419402308849/100000000000000000000)
  directionHi := (9054657388388046177/2000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree083.table
  base := (32984239007626308003274241870916241757239/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6930000000000000000000000000000000000000000
      center := (54054)
      previous := (27027)
      next := (27027)
      square := (715482298423144611188018135100000000000000)
      linear := (-58622855213856925959334202556105000000000000)
      constant := (1223670129318413582979897017539859955537766627) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree083.table
  base := (16492003417944111355966637036725362485607/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8910000000000000000000000000000000000000000
      center := (69498)
      previous := (34749)
      next := (34749)
      square := (919905812258328785813166173700000000000000)
      linear := (-75568985827467256920974764223385000000000000)
      constant := (1581360538885355695869737413263849595949351674) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree083.checked
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
end ForestUnimodality.Stage80KernelData.Cell076.Kernel083

namespace ForestUnimodality.Stage80KernelData.Cell076.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (452732869419402308849/100000000000000000000)
  centralHi := (9054657388388046177/2000000000000000000)
  directionLo := (18219402810687090419/4000000000000000000)
  directionHi := (113871267566794315119/25000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree084.table
  base := (34192448708258006015126103359689021828013/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 770000000000000000000000000000000000000000
      center := (6006)
      previous := (3003)
      next := (3003)
      square := (79498033158127179020890903900000000000000)
      linear := (-6592140752438617443001791828895000000000000)
      constant := (139291289536865426147479868290351054680757001) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree084.table
  base := (34192236968434874079120719963401760552257/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 990000000000000000000000000000000000000000
      center := (7722)
      previous := (3861)
      next := (3861)
      square := (102211756917592087312574019300000000000000)
      linear := (-8497733295758220714013683437865000000000000)
      constant := (180007250803478851766056274129236774294673443) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree084.checked
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
end ForestUnimodality.Stage80KernelData.Cell076.Kernel084

namespace ForestUnimodality.Stage80KernelData.Cell076.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18219402810687090419/4000000000000000000)
  centralHi := (113871267566794315119/25000000000000000000)
  directionLo := (114555185232889292003/25000000000000000000)
  directionHi := (458220740931557168013/100000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree085.table
  base := (17708050540862452901599508143945952449537/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 48510000000000000000000000000000000000000000
      center := (378378)
      previous := (189189)
      next := (189189)
      square := (5008376088962012278316126945700000000000000)
      linear := (-420249748310267316102886352548035000000000000)
      constant := (8987527584173785797530312670547101130665407974) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree085.table
  base := (1106747125096998293894623709260379352519/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 8910000000000000000000000000000000000000000
      center := (69498)
      previous := (34749)
      next := (34749)
      square := (919905812258328785813166173700000000000000)
      linear := (-77390213496180715931271537658185000000000000)
      constant := (1659234441278463598422868466072906936099021728) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree085.checked
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
end ForestUnimodality.Stage80KernelData.Cell076.Kernel085

namespace ForestUnimodality.Stage80KernelData.Cell076.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114555185232889292003/25000000000000000000)
  centralHi := (458220740931557168013/100000000000000000000)
  directionLo := (460940175731553101511/100000000000000000000)
  directionHi := (57617521966444137689/12500000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree086.table
  base := (9163796650638560257320511118951764870707/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 48510000000000000000000000000000000000000000
      center := (378378)
      previous := (189189)
      next := (189189)
      square := (5008376088962012278316126945700000000000000)
      linear := (-425194629216901733296659819875685000000000000)
      constant := (9202219889074618542069860776136162545551198628) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree086.table
  base := (18327505282420293202806433214642593588353/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8910000000000000000000000000000000000000000
      center := (69498)
      previous := (34749)
      next := (34749)
      square := (919905812258328785813166173700000000000000)
      linear := (-78300827330537445436419924375585000000000000)
      constant := (1698868082673643621852811077649103101774445046) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree086.checked
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
end ForestUnimodality.Stage80KernelData.Cell076.Kernel086

namespace ForestUnimodality.Stage80KernelData.Cell076.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (460940175731553101511/100000000000000000000)
  centralHi := (57617521966444137689/12500000000000000000)
  directionLo := (23182183017729633079/5000000000000000000)
  directionHi := (463643660354592661581/100000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree087.table
  base := (18954848342916676028178100405671673920947/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5390000000000000000000000000000000000000000
      center := (42042)
      previous := (21021)
      next := (21021)
      square := (556486232106890253146236327300000000000000)
      linear := (-47793278902615127832270365244815000000000000)
      constant := (1046603123764400974334521879175394064486780866) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree087.table
  base := (37909536206715152473829181144218201125123/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 990000000000000000000000000000000000000000
      center := (7722)
      previous := (3861)
      next := (3861)
      square := (102211756917592087312574019300000000000000)
      linear := (-8801271240543797215729812343665000000000000)
      constant := (193218463765626158093154098048182601911387177) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree087.checked
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
end ForestUnimodality.Stage80KernelData.Cell076.Kernel087

namespace ForestUnimodality.Stage80KernelData.Cell076.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23182183017729633079/5000000000000000000)
  centralHi := (463643660354592661581/100000000000000000000)
  directionLo := (233165736103407088459/50000000000000000000)
  directionHi := (466331472206814176919/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree088.table
  base := (3917962359434256142358505154211655635977/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (34398)
      previous := (17199)
      next := (17199)
      square := (455306917178364752574193358700000000000000)
      linear := (-39553126457288233425836977684635000000000000)
      constant := (876286565550500347544573049067403401354658570) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree088.table
  base := (9794869329511156689619670734340722711249/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (6318)
      previous := (3159)
      next := (3159)
      square := (83627801114393525983015106700000000000000)
      linear := (-7283823181750082222428790710035000000000000)
      constant := (161775337104392766669594060590206394158444676) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree088.checked
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
end ForestUnimodality.Stage80KernelData.Cell076.Kernel088

namespace ForestUnimodality.Stage80KernelData.Cell076.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (233165736103407088459/50000000000000000000)
  centralHi := (466331472206814176919/100000000000000000000)
  directionLo := (234501940372646238431/50000000000000000000)
  directionHi := (469003880745292476863/100000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree089.table
  base := (40464960354857202334353334091159053781863/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 48510000000000000000000000000000000000000000
      center := (378378)
      previous := (189189)
      next := (189189)
      square := (5008376088962012278316126945700000000000000)
      linear := (-440029271936804984877980221858635000000000000)
      constant := (9861392176775190845378300018863965069895817413) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree089.table
  base := (10116206760402317535964055820799315975443/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8910000000000000000000000000000000000000000
      center := (69498)
      previous := (34749)
      next := (34749)
      square := (919905812258328785813166173700000000000000)
      linear := (-81032668833607633951865084527785000000000000)
      constant := (1820555679336915865882161142488743762136478852) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree089.checked
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
end ForestUnimodality.Stage80KernelData.Cell076.Kernel089

namespace ForestUnimodality.Stage80KernelData.Cell076.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (234501940372646238431/50000000000000000000)
  centralHi := (469003880745292476863/100000000000000000000)
  directionLo := (471661147793322437757/100000000000000000000)
  directionHi := (235830573896661218879/50000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree090.table
  base := (41765700682713499670709121710996221242847/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 770000000000000000000000000000000000000000
      center := (6006)
      previous := (3003)
      next := (3003)
      square := (79498033158127179020890903900000000000000)
      linear := (-7063081791165704794789741098195000000000000)
      constant := (160097586516694696239325421480859209035699219) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree090.table
  base := (208827895995320768566623650692058507853/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 110000000000000000000000000000000000000000
      center := (858)
      previous := (429)
      next := (429)
      square := (11356861879732454145841557700000000000000)
      linear := (-1011645465036597079716215694385000000000000)
      constant := (22988235579648350478068428138672528717276600) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree090.checked
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
end ForestUnimodality.Stage80KernelData.Cell076.Kernel090

namespace ForestUnimodality.Stage80KernelData.Cell076.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (471661147793322437757/100000000000000000000)
  centralHi := (235830573896661218879/50000000000000000000)
  directionLo := (474303527839804471837/100000000000000000000)
  directionHi := (237151763919902235919/50000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree091.table
  base := (10770459728455596469560908357452868351343/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6930000000000000000000000000000000000000000
      center := (54054)
      previous := (27027)
      next := (27027)
      square := (715482298423144611188018135100000000000000)
      linear := (-64274147678581974180789593787705000000000000)
      constant := (1473345644986961829911638735219664351069922796) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree091.table
  base := (21540864111867176949933007558890116611313/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (6318)
      previous := (3159)
      next := (3159)
      square := (83627801114393525983015106700000000000000)
      linear := (-7532172409301917542014714360235000000000000)
      constant := (173091173730201331362860551897475198891032706) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree091.checked
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
end ForestUnimodality.Stage80KernelData.Cell076.Kernel091

namespace ForestUnimodality.Stage80KernelData.Cell076.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (474303527839804471837/100000000000000000000)
  centralHi := (237151763919902235919/50000000000000000000)
  directionLo := (95386253664740183011/20000000000000000000)
  directionHi := (29808204270231307191/6250000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree092.table
  base := (5551671242924486489347963843120942741187/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (34398)
      previous := (17199)
      next := (17199)
      square := (455306917178364752574193358700000000000000)
      linear := (-41351264968791657859936420349235000000000000)
      constant := (958473349552978658769693346063475685990907736) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree092.table
  base := (5551658637507861697609730667800396115311/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8910000000000000000000000000000000000000000
      center := (69498)
      previous := (34749)
      next := (34749)
      square := (919905812258328785813166173700000000000000)
      linear := (-83764510336677822467310244679985000000000000)
      constant := (1946423162110149368069692727912901223509936808) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree092.checked
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
end ForestUnimodality.Stage80KernelData.Cell076.Kernel092

namespace ForestUnimodality.Stage80KernelData.Cell076.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (95386253664740183011/20000000000000000000)
  centralHi := (29808204270231307191/6250000000000000000)
  directionLo := (239772304952231620333/50000000000000000000)
  directionHi := (479544609904463240667/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree093.table
  base := (11440072292680839408188219496978082819721/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5390000000000000000000000000000000000000000
      center := (42042)
      previous := (21021)
      next := (21021)
      square := (556486232106890253146236327300000000000000)
      linear := (-51089866173704739294786010129915000000000000)
      constant := (1197278879861757306884119450034192246559318476) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree093.table
  base := (22880098654526433111493779179499320605867/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 990000000000000000000000000000000000000000
      center := (7722)
      previous := (3861)
      next := (3861)
      square := (102211756917592087312574019300000000000000)
      linear := (-9408347130114950219162070155265000000000000)
      constant := (221034203462099368248554178678735865479961666) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree093.checked
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
end ForestUnimodality.Stage80KernelData.Cell076.Kernel093

namespace ForestUnimodality.Stage80KernelData.Cell076.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (239772304952231620333/50000000000000000000)
  centralHi := (479544609904463240667/100000000000000000000)
  directionLo := (482143786719266608649/100000000000000000000)
  directionHi := (9642875734385332173/2000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree094.table
  base := (47122592449400141751421676266930054784753/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 48510000000000000000000000000000000000000000
      center := (378378)
      previous := (189189)
      next := (189189)
      square := (5008376088962012278316126945700000000000000)
      linear := (-464753676469977070846847558496885000000000000)
      constant := (11010328715813675440999997272282430195760836803) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree094.table
  base := (23561254389555185855919314408109071620979/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8910000000000000000000000000000000000000000
      center := (69498)
      previous := (34749)
      next := (34749)
      square := (919905812258328785813166173700000000000000)
      linear := (-85585738005391281477607018114785000000000000)
      constant := (2032656914550659318491459047371340365628584578) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree094.checked
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
end ForestUnimodality.Stage80KernelData.Cell076.Kernel094

namespace ForestUnimodality.Stage80KernelData.Cell076.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (482143786719266608649/100000000000000000000)
  centralHi := (9642875734385332173/2000000000000000000)
  directionLo := (484729026627829945521/100000000000000000000)
  directionHi := (242364513313914972761/50000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree095.table
  base := (24250138021235243360974430912758355091991/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 48510000000000000000000000000000000000000000
      center := (378378)
      previous := (189189)
      next := (189189)
      square := (5008376088962012278316126945700000000000000)
      linear := (-469698557376611488040621025824535000000000000)
      constant := (11247663218128371903725964599159531561102496682) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree095.table
  base := (48500199841753630708682826767744068824771/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8910000000000000000000000000000000000000000
      center := (69498)
      previous := (34749)
      next := (34749)
      square := (919905812258328785813166173700000000000000)
      linear := (-86496351839748010982755404832185000000000000)
      constant := (2076470409016827115442282372818884965322870961) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree095.checked
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
end ForestUnimodality.Stage80KernelData.Cell076.Kernel095

namespace ForestUnimodality.Stage80KernelData.Cell076.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (484729026627829945521/100000000000000000000)
  centralHi := (242364513313914972761/50000000000000000000)
  directionLo := (243650275722773037323/50000000000000000000)
  directionHi := (487300551445546074647/100000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree096.table
  base := (24946668290999673084047333389491314793949/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5390000000000000000000000000000000000000000
      center := (42042)
      previous := (21021)
      next := (21021)
      square := (556486232106890253146236327300000000000000)
      linear := (-52738159809249545026043832572465000000000000)
      constant := (1276390378818005804462648657436711637347877022) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree096.table
  base := (49893267191706568073598528533769497327611/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 990000000000000000000000000000000000000000
      center := (7722)
      previous := (3861)
      next := (3861)
      square := (102211756917592087312574019300000000000000)
      linear := (-9711885074900526720878199061065000000000000)
      constant := (235638701290266302459976379750283180235433489) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree096.checked
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
end ForestUnimodality.Stage80KernelData.Cell076.Kernel096

namespace ForestUnimodality.Stage80KernelData.Cell076.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (243650275722773037323/50000000000000000000)
  centralHi := (487300551445546074647/100000000000000000000)
  directionLo := (244929288582798484759/50000000000000000000)
  directionHi := (489858577165596969519/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree097.table
  base := (51301771032635887093391588225718008455647/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 990000000000000000000000000000000000000000
      center := (7722)
      previous := (3861)
      next := (3861)
      square := (102211756917592087312574019300000000000000)
      linear := (-9787516718160822906697305315915000000000000)
      constant := (239385291322249582845872517735088582837109053) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree097.table
  base := (51301707850942840661858425508923906977037/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8910000000000000000000000000000000000000000
      center := (69498)
      previous := (34749)
      next := (34749)
      square := (919905812258328785813166173700000000000000)
      linear := (-88317579508461469993052178266985000000000000)
      constant := (2165490619683946666842022150204946201116539967) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree097.checked
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
end ForestUnimodality.Stage80KernelData.Cell076.Kernel097

namespace ForestUnimodality.Stage80KernelData.Cell076.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244929288582798484759/50000000000000000000)
  centralHi := (489858577165596969519/100000000000000000000)
  directionLo := (492403314170683608417/100000000000000000000)
  directionHi := (246201657085341804209/50000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree098.table
  base := (52725576658774553815596930090104145489009/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 990000000000000000000000000000000000000000
      center := (7722)
      previous := (3861)
      next := (3861)
      square := (102211756917592087312574019300000000000000)
      linear := (-9888432655030913053509008730765000000000000)
      constant := (244382873492703700223737788505377810403411891) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree098.table
  base := (10545103827257849847365383384637839800253/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8910000000000000000000000000000000000000000
      center := (69498)
      previous := (34749)
      next := (34749)
      square := (919905812258328785813166173700000000000000)
      linear := (-89228193342818199498200564984385000000000000)
      constant := (2210697330840769629029144249889991576310127115) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree098.checked
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
end ForestUnimodality.Stage80KernelData.Cell076.Kernel098
