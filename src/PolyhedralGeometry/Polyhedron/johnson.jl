function _johnson_solid(::Val{9})
  Qx, x = QQ["x"]
  NF, sr5 = number_field(x^2 - 5)
  NFy, y = NF["y"]
  MF, mr = number_field(y^2 - (5 + sr5)//10)
  EMF, mre = Hecke.embedded_field(MF, real_embeddings(MF)[4])
  sre5 = EMF(sr5)
  V = [1//2 -mre*(sre5+1)//4 1//2;
       1//2 -mre*(sre5+1)//4 -1//2;
       -1//2 -mre*(sre5+1)//4 1//2;
       -1//2 -mre*(sre5+1)//4 -1//2;
       (1+sre5)//4 mre*(sre5-1)//4 1//2;
       (1+sre5)//4 mre*(sre5-1)//4 -1//2;
       -(1+sre5)//4 mre*(sre5-1)//4 1//2;
       -(1+sre5)//4 mre*(sre5-1)//4 -1//2;
       0 mre 1//2;
       0 mre -1//2;
       0 0 (1+mre*(sre5-1))//2]
  return convex_hull(EMF, V; non_redundant = true)
end

function _johnson_solid(::Val{10})
  Qx, x = QQ["x"]
  NF, qr8 = number_field(x^4 - 8)
  ENF, qre8 = Hecke.embedded_field(NF, real_embeddings(NF)[2])
  sre2 = (qre8^2)//2
  V = [0 0 (2*sre2 + qre8)//4;
       1//2 1//2 qre8//4;
       1//2 -1//2 qre8//4;
       -1//2 1//2 qre8//4;
       -1//2 -1//2 qre8//4;
       0 sre2//2 -qre8//4;
       0 -sre2//2 -qre8//4;
       sre2//2 0 -qre8//4;
       -sre2//2 0 -qre8//4]
  return convex_hull(ENF, V; non_redundant = true)
end

function _johnson_solid(::Val{13})
  Qx, x = QQ["x"]
  NF, sr5 = number_field(x^2 - 5)
  NFy, y = NF["y"]
  MF, mr = number_field(y^2 - (5 + sr5)//10)
  EMF, mre = Hecke.embedded_field(MF, real_embeddings(MF)[4])
  sre5 = EMF(sr5)
  V = [1//2 -mre*(sre5+1)//4 0;
       -1//2 -mre*(sre5+1)//4 0;
       (1+sre5)//4 mre*(sre5-1)//4 0;
       -(1+sre5)//4 mre*(sre5-1)//4 0;
       0 mre 0;
       0 0 mre*(sre5-1)//2;
       0 0 -mre*(sre5-1)//2]
  return convex_hull(EMF, V; non_redundant = true)
end

function _johnson_solid(::Val{16})
  Qx, x = QQ["x"]
  NF, sr5 = number_field(x^2 - 5)
  NFy, y = NF["y"]
  MF, mr = number_field(y^2 - (5 + sr5)//10)
  EMF, mre = Hecke.embedded_field(MF, real_embeddings(MF)[4])
  sre5 = EMF(sr5)
  V = [1//2 -mre*(sre5+1)//4 1//2;
       1//2 -mre*(sre5+1)//4 -1//2;
       -1//2 -mre*(sre5+1)//4 1//2;
       -1//2 -mre*(sre5+1)//4 -1//2;
       (1+sre5)//4 mre*(sre5-1)//4 1//2;
       (1+sre5)//4 mre*(sre5-1)//4 -1//2;
       -(1+sre5)//4 mre*(sre5-1)//4 1//2;
       -(1+sre5)//4 mre*(sre5-1)//4 -1//2;
       0 mre 1//2;
       0 mre -1//2;
       0 0 (1+mre*(sre5-1))//2;
       0 0 -(1+mre*(sre5-1))//2]
  return convex_hull(EMF, V; non_redundant = true)
end

function _johnson_solid(::Val{17})
  Qx, x = QQ["x"]
  NF, qr8 = number_field(x^4 - 8)
  ENF, qre8 = Hecke.embedded_field(NF, real_embeddings(NF)[2])
  sre2 = (qre8^2)//2
  V = [0 0 (2*sre2 + qre8)//4;
       0 0 -(2*sre2 + qre8)//4;
       1//2 1//2 qre8//4;
       1//2 -1//2 qre8//4;
       -1//2 1//2 qre8//4;
       -1//2 -1//2 qre8//4;
       0 sre2//2 -qre8//4;
       0 -sre2//2 -qre8//4;
       sre2//2 0 -qre8//4;
       -sre2//2 0 -qre8//4]
  return convex_hull(ENF, V; non_redundant = true)
end

function _johnson_solid(::Val{18})
  Qx, x = QQ["x"]
  NF, srv = number_field([x^2 - 2, x^2 - 3])
  ENF, srev = Hecke.embedded_field(NF, real_embeddings(NF)[4])
  sre2, sre3 = srev
  V = [1//2 sre3//2 1//2;
       1//2 sre3//2 -1//2;
       1//2 -sre3//2 1//2;
       1//2 -sre3//2 -1//2;
       -1//2 sre3//2 1//2;
       -1//2 sre3//2 -1//2;
       -1//2 -sre3//2 1//2;
       -1//2 -sre3//2 -1//2;
       1 0 1//2;
       1 0 -1//2;
       -1 0 1//2;
       -1 0 -1//2;
       1//2 -sre3//6 (3+2*sre2*sre3)//6;
       -1//2 -sre3//6 (3+2*sre2*sre3)//6;
       0 sre3//3 (3+2*sre2*sre3)//6]
  return convex_hull(ENF, V; non_redundant = true)
end

function _johnson_solid(::Val{20})
  Qx, x = QQ["x"]
  NF, sr5 = number_field(x^2 - 5)
  NFy, y = NF["y"]
  MF, mr = number_field(y^2 - (5 + sr5)//10)
  EMF, mre = Hecke.embedded_field(MF, real_embeddings(MF)[4])
  sre5 = EMF(sr5)
  V = [1//2 mre*(sre5+5)//4 1//2;
       1//2 mre*(sre5+5)//4 -1//2;
       1//2 -mre*(sre5+5)//4 1//2;
       1//2 -mre*(sre5+5)//4 -1//2;
       -1//2 mre*(sre5+5)//4 1//2;
       -1//2 mre*(sre5+5)//4 -1//2;
       -1//2 -mre*(sre5+5)//4 1//2;
       -1//2 -mre*(sre5+5)//4 -1//2;
       (3+sre5)//4 sre5*mre//2 1//2;
       (3+sre5)//4 sre5*mre//2 -1//2;
       (3+sre5)//4 -sre5*mre//2 1//2;
       (3+sre5)//4 -sre5*mre//2 -1//2;
       -(3+sre5)//4 sre5*mre//2 1//2;
       -(3+sre5)//4 sre5*mre//2 -1//2;
       -(3+sre5)//4 -sre5*mre//2 1//2;
       -(3+sre5)//4 -sre5*mre//2 -1//2;
       (1+sre5)//2 0 1//2;
       (1+sre5)//2 0 -1//2;
       -(1+sre5)//2 0 1//2;
       -(1+sre5)//2 0 -1//2;
       1//2 -mre*(sre5+1)//4 (1+mre*(sre5-1))//2;
       -1//2 -mre*(sre5+1)//4 (1+mre*(sre5-1))//2;
       (1+sre5)//4 mre*(sre5-1)//4 (1+mre*(sre5-1))//2;
       -(1+sre5)//4 mre*(sre5-1)//4 (1+mre*(sre5-1))//2;
       0 mre (1+mre*(sre5-1))//2]
  return convex_hull(EMF, V; non_redundant = true)
end

function _johnson_solid(::Val{21})
  Qx, x = QQ["x"]
  NF, sr5 = number_field(x^2 - 5)
  NFy, y = NF["y"]
  MF, mr = number_field(y^2 - (5 + sr5)//10)
  EMF, mre = Hecke.embedded_field(MF, real_embeddings(MF)[4])
  sre5 = EMF(sr5)
  V = [1//2 mre*(sre5+5)//4 1//2;
       1//2 mre*(sre5+5)//4 -1//2;
       1//2 -mre*(sre5+5)//4 1//2;
       1//2 -mre*(sre5+5)//4 -1//2;
       -1//2 mre*(sre5+5)//4 1//2;
       -1//2 mre*(sre5+5)//4 -1//2;
       -1//2 -mre*(sre5+5)//4 1//2;
       -1//2 -mre*(sre5+5)//4 -1//2;
       (3+sre5)//4 sre5*mre//2 1//2;
       (3+sre5)//4 sre5*mre//2 -1//2;
       (3+sre5)//4 -sre5*mre//2 1//2;
       (3+sre5)//4 -sre5*mre//2 -1//2;
       -(3+sre5)//4 sre5*mre//2 1//2;
       -(3+sre5)//4 sre5*mre//2 -1//2;
       -(3+sre5)//4 -sre5*mre//2 1//2;
       -(3+sre5)//4 -sre5*mre//2 -1//2;
       (1+sre5)//2 0 1//2;
       (1+sre5)//2 0 -1//2;
       -(1+sre5)//2 0 1//2;
       -(1+sre5)//2 0 -1//2;
       0 mre (1+mre*(sre5+1))//2;
       1//2 -mre*(sre5+1)//4 (1+mre*(sre5+1))//2;
       -1//2 -mre*(sre5+1)//4 (1+mre*(sre5+1))//2;
       (1+sre5)//4 mre*(sre5-1)//4 (1+mre*(sre5+1))//2;
       -(1+sre5)//4 mre*(sre5-1)//4 (1+mre*(sre5+1))//2;
       0 -mre*(sre5+1)//2 (1+2*mre)//2;
       (1+sre5)//4 mre*(sre5+3)//4 (1+2*mre)//2;
       -(1+sre5)//4 mre*(sre5+3)//4 (1+2*mre)//2;
       (3+sre5)//4 -mre//2 (1+2*mre)//2;
       -(3+sre5)//4 -mre//2 (1+2*mre)//2]
  return convex_hull(EMF, V; non_redundant = true)
end

function _johnson_solid(::Val{22})
  Qx, x = QQ["x"]
  NF, srv = number_field([x^2 - 2, x^2 - 3])
  sr2, sr3 = srv
  NFy, y = NF["y"]
  MF, mr = number_field(y^2 - (sr3-1))
  EMF, mre = Hecke.embedded_field(MF, real_embeddings(MF)[4])
  sre2 = EMF(sr2)
  sre3 = EMF(sr3)
  V = [1//2 -sre3//6 (2*sre2*sre3+3*mre)//6;
       -1//2 -sre3//6 (2*sre2*sre3+3*mre)//6;
       0 sre3//3 (2*sre2*sre3+3*mre)//6;
       1//2 sre3//2 mre//2;
       1//2 -sre3//2 mre//2;
       -1//2 sre3//2 mre//2;
       -1//2 -sre3//2 mre//2;
       1 0 mre//2;
       -1 0 mre//2;
       sre3//2 1//2 -mre//2;
       sre3//2 -1//2 -mre//2;
       -sre3//2 1//2 -mre//2;
       -sre3//2 -1//2 -mre//2;
       0 1 -mre//2;
       0 -1 -mre//2]
  return convex_hull(EMF, V; non_redundant = true)
end

function _johnson_solid(::Val{23})
  Qx, x = QQ["x"]
  NF, sr2 = number_field(x^2 - 2)
  NFy, y = NF["y"]
  MF, mr = number_field(y^2 - (sr2+2))
  MFz, z = MF["z"]
  LF, lr = number_field(z^2 - (-2 - 2*sr2 + (sr2+2)*mr)//8)
  ELF, lre = Hecke.embedded_field(LF, real_embeddings(LF)[6])
  sre2 = ELF(sr2)
  mre = ELF(mr)
  V = [1//2 1//2 (sre2+2*lre)//2;
       1//2 -1//2 (sre2+2*lre)//2;
       -1//2 1//2 (sre2+2*lre)//2;
       -1//2 -1//2 (sre2+2*lre)//2;
       1//2 (1+sre2)//2 lre;
       1//2 -(1+sre2)//2 lre;
       -1//2 (1+sre2)//2 lre;
       -1//2 -(1+sre2)//2 lre;
       (1+sre2)//2 1//2 lre;
       (1+sre2)//2 -1//2 lre;
       -(1+sre2)//2 1//2 lre;
       -(1+sre2)//2 -1//2 lre;
       0 mre//sre2 -lre;
       0 -mre//sre2 -lre;
       mre//sre2 0 -lre;
       -mre//sre2 0 -lre;
       mre//2 mre//2 -lre;
       mre//2 -mre//2 -lre;
       -mre//2 mre//2 -lre;
       -mre//2 -mre//2 -lre]
  return convex_hull(ELF, V; non_redundant = true)
end

function _johnson_solid(::Val{24})
  Qx, x = QQ["x"]
  NF, sr5 = number_field(x^2 - 5)
  NFy, y = NF["y"]
  MF, mr = number_field(y^2 - (5 + sr5)//10)
  MFz, z = MF["z"]
  LF, lr = number_field(z^2 - (-4 - 2*sr5 + (3*sr5+5)*mr)//8)
  ELF, lre = Hecke.embedded_field(LF, real_embeddings(LF)[4])
  sre5 = ELF(sr5)
  mre = ELF(mr)
  V = [1//2 -mre*(sre5+1)//4 mre*(sre5-1)//2+lre;
       -1//2 -mre*(sre5+1)//4 mre*(sre5-1)//2+lre;
       (1+sre5)//4 mre*(sre5-1)//4 mre*(sre5-1)//2+lre;
       -(1+sre5)//4 mre*(sre5-1)//4 mre*(sre5-1)//2+lre;
       0 mre mre*(sre5-1)//2+lre;
       1//2 mre*(sre5+5)//4 lre;
       1//2 -mre*(sre5+5)//4 lre;
       -1//2 mre*(sre5+5)//4 lre;
       -1//2 -mre*(sre5+5)//4 lre;
       (3+sre5)//4 sre5*mre//2 lre;
       (3+sre5)//4 -sre5*mre//2 lre;
       -(3+sre5)//4 sre5*mre//2 lre;
       -(3+sre5)//4 -sre5*mre//2 lre;
       (1+sre5)//2 0 lre;
       -(1+sre5)//2 0 lre;
       mre*(sre5+5)//4 1//2 -lre;
       mre*(sre5+5)//4 -1//2 -lre;
       -mre*(sre5+5)//4 1//2 -lre;
       -mre*(sre5+5)//4 -1//2 -lre;
       sre5*mre//2 (3+sre5)//4 -lre;
       sre5*mre//2 -(3+sre5)//4 -lre;
       -sre5*mre//2 (3+sre5)//4 -lre;
       -sre5*mre//2 -(3+sre5)//4 -lre;
       0 (1+sre5)//2 -lre;
       0 -(1+sre5)//2 -lre]
  return convex_hull(ELF, V; non_redundant = true)
end

function _johnson_solid(::Val{25})
  Qx, x = QQ["x"]
  NF, sr5 = number_field(x^2 - 5)
  NFy, y = NF["y"]
  MF, mr = number_field(y^2 - (5 + sr5)//10)
  MFz, z = MF["z"]
  LF, lr = number_field(z^2 - (-4 - 2*sr5 + (3*sr5+5)*mr)//8)
  ELF, lre = Hecke.embedded_field(LF, real_embeddings(LF)[4])
  sre5 = ELF(sr5)
  mre = ELF(mr)
  V = [1//2 -mre*(sre5+1)//4 mre*(sre5+1)//2+lre;
       -1//2 -mre*(sre5+1)//4 mre*(sre5+1)//2+lre;
       (1+sre5)//4 mre*(sre5-1)//4 mre*(sre5+1)//2+lre;
       -(1+sre5)//4 mre*(sre5-1)//4 mre*(sre5+1)//2+lre;
       0 mre mre*(sre5+1)//2+lre;
       (1+sre5)//4 mre*(sre5+3)//4 mre+lre;
       -(1+sre5)//4 mre*(sre5+3)//4 mre+lre;
       (3+sre5)//4 -mre//2 mre+lre;
       -(3+sre5)//4 -mre//2 mre+lre;
       0 -mre*(sre5+1)//2 mre+lre;
       1//2 mre*(sre5+5)//4 lre;
       1//2 -mre*(sre5+5)//4 lre;
       -1//2 mre*(sre5+5)//4 lre;
       -1//2 -mre*(sre5+5)//4 lre;
       (3+sre5)//4 sre5*mre//2 lre;
       (3+sre5)//4 -sre5*mre//2 lre;
       -(3+sre5)//4 sre5*mre//2 lre;
       -(3+sre5)//4 -sre5*mre//2 lre;
       (1+sre5)//2 0 lre;
       -(1+sre5)//2 0 lre;
       mre*(sre5+5)//4 1//2 -lre;
       mre*(sre5+5)//4 -1//2 -lre;
       -mre*(sre5+5)//4 1//2 -lre;
       -mre*(sre5+5)//4 -1//2 -lre;
       sre5*mre//2 (3+sre5)//4 -lre;
       sre5*mre//2 -(3+sre5)//4 -lre;
       -sre5*mre//2 (3+sre5)//4 -lre;
       -sre5*mre//2 -(3+sre5)//4 -lre;
       0 (1+sre5)//2 -lre;
       0 -(1+sre5)//2 -lre]
  return convex_hull(ELF, V; non_redundant = true)
end

function _johnson_solid(::Val{30})
  Qx, x = QQ["x"]
  NF, sr5 = number_field(x^2 - 5)
  NFy, y = NF["y"]
  MF, mr = number_field(y^2 - (5 + sr5)//10)
  EMF, mre = Hecke.embedded_field(MF, real_embeddings(MF)[4])
  sre5 = EMF(sr5)
  V = [1//2 -mre*(sre5+1)//4 mre*(sre5-1)//2;
       1//2 -mre*(sre5+1)//4 -mre*(sre5-1)//2;
       -1//2 -mre*(sre5+1)//4 mre*(sre5-1)//2;
       -1//2 -mre*(sre5+1)//4 -mre*(sre5-1)//2;
       (1+sre5)//4 mre*(sre5-1)//4 mre*(sre5-1)//2;
       (1+sre5)//4 mre*(sre5-1)//4 -mre*(sre5-1)//2;
       -(1+sre5)//4 mre*(sre5-1)//4 mre*(sre5-1)//2;
       -(1+sre5)//4 mre*(sre5-1)//4 -mre*(sre5-1)//2;
       0 mre mre*(sre5-1)//2;
       0 mre -mre*(sre5-1)//2;
       1//2 mre*(sre5+5)//4 0;
       1//2 -mre*(sre5+5)//4 0;
       -1//2 mre*(sre5+5)//4 0;
       -1//2 -mre*(sre5+5)//4 0;
       (3+sre5)//4 sre5*mre//2 0;
       (3+sre5)//4 -sre5*mre//2 0;
       -(3+sre5)//4 sre5*mre//2 0;
       -(3+sre5)//4 -sre5*mre//2 0;
       (1+sre5)//2 0 0;
       -(1+sre5)//2 0 0]
  return convex_hull(EMF, V; non_redundant = true)
end

function _johnson_solid(::Val{32})
  Qx, x = QQ["x"]
  NF, sr5 = number_field(x^2 - 5)
  NFy, y = NF["y"]
  MF, mr = number_field(y^2 - (5 + sr5)//10)
  EMF, mre = Hecke.embedded_field(MF, real_embeddings(MF)[4])
  sre5 = EMF(sr5)
  V = [0 mre mre*(sre5+1)//2;
       1//2 -mre*(sre5+1)//4 mre*(sre5+1)//2;
       -1//2 -mre*(sre5+1)//4 mre*(sre5+1)//2;
       (1+sre5)//4 mre*(sre5-1)//4 mre*(sre5+1)//2;
       -(1+sre5)//4 mre*(sre5-1)//4 mre*(sre5+1)//2;
       0 -mre*(sre5+1)//2 mre;
       (1+sre5)//4 mre*(sre5+3)//4 mre;
       -(1+sre5)//4 mre*(sre5+3)//4 mre;
       (3+sre5)//4 -mre//2 mre;
       -(3+sre5)//4 -mre//2 mre;
       1//2 mre*(sre5+5)//4 0;
       1//2 -mre*(sre5+5)//4 0;
       -1//2 mre*(sre5+5)//4 0;
       -1//2 -mre*(sre5+5)//4 0;
       (3+sre5)//4 sre5*mre//2 0;
       (3+sre5)//4 -sre5*mre//2 0;
       -(3+sre5)//4 sre5*mre//2 0;
       -(3+sre5)//4 -sre5*mre//2 0;
       (1+sre5)//2 0 0;
       -(1+sre5)//2 0 0;
       1//2 -mre*(sre5+1)//4 -mre*(sre5-1)//2;
       -1//2 -mre*(sre5+1)//4 -mre*(sre5-1)//2;
       (1+sre5)//4 mre*(sre5-1)//4 -mre*(sre5-1)//2;
       -(1+sre5)//4 mre*(sre5-1)//4 -mre*(sre5-1)//2;
       0 mre -mre*(sre5-1)//2]
  return convex_hull(EMF, V; non_redundant = true)
end

function _johnson_solid(::Val{33})
  Qx, x = QQ["x"]
  NF, sr5 = number_field(x^2 - 5)
  NFy, y = NF["y"]
  MF, mr = number_field(y^2 - (5 + sr5)//10)
  EMF, mre = Hecke.embedded_field(MF, real_embeddings(MF)[4])
  sre5 = EMF(sr5)
  V = [0 mre mre*(sre5+1)//2;
       1//2 -mre*(sre5+1)//4 mre*(sre5+1)//2;
       -1//2 -mre*(sre5+1)//4 mre*(sre5+1)//2;
       (1+sre5)//4 mre*(sre5-1)//4 mre*(sre5+1)//2;
       -(1+sre5)//4 mre*(sre5-1)//4 mre*(sre5+1)//2;
       0 -mre*(sre5+1)//2 mre;
       (1+sre5)//4 mre*(sre5+3)//4 mre;
       -(1+sre5)//4 mre*(sre5+3)//4 mre;
       (3+sre5)//4 -mre//2 mre;
       -(3+sre5)//4 -mre//2 mre;
       1//2 mre*(sre5+5)//4 0;
       1//2 -mre*(sre5+5)//4 0;
       -1//2 mre*(sre5+5)//4 0;
       -1//2 -mre*(sre5+5)//4 0;
       (3+sre5)//4 sre5*mre//2 0;
       (3+sre5)//4 -sre5*mre//2 0;
       -(3+sre5)//4 sre5*mre//2 0;
       -(3+sre5)//4 -sre5*mre//2 0;
       (1+sre5)//2 0 0;
       -(1+sre5)//2 0 0;
       1//2 mre*(sre5+1)//4 -mre*(sre5-1)//2;
       -1//2 mre*(sre5+1)//4 -mre*(sre5-1)//2;
       (1+sre5)//4 -mre*(sre5-1)//4 -mre*(sre5-1)//2;
       -(1+sre5)//4 -mre*(sre5-1)//4 -mre*(sre5-1)//2;
       0 -mre -mre*(sre5-1)//2]
  return convex_hull(EMF, V; non_redundant = true)
end

function _johnson_solid(::Val{34})
  Qx, x = QQ["x"]
  NF, sr5 = number_field(x^2 - 5)
  NFy, y = NF["y"]
  MF, mr = number_field(y^2 - (5 + sr5)//10)
  EMF, mre = Hecke.embedded_field(MF, real_embeddings(MF)[4])
  sre5 = EMF(sr5)
  V = [0 mre mre*(sre5+1)//2;
       0 mre -mre*(sre5+1)//2;
       1//2 -mre*(sre5+1)//4 mre*(sre5+1)//2;
       1//2 -mre*(sre5+1)//4 -mre*(sre5+1)//2;
       -1//2 -mre*(sre5+1)//4 mre*(sre5+1)//2;
       -1//2 -mre*(sre5+1)//4 -mre*(sre5+1)//2;
       (1+sre5)//4 mre*(sre5-1)//4 mre*(sre5+1)//2;
       (1+sre5)//4 mre*(sre5-1)//4 -mre*(sre5+1)//2;
       -(1+sre5)//4 mre*(sre5-1)//4 mre*(sre5+1)//2;
       -(1+sre5)//4 mre*(sre5-1)//4 -mre*(sre5+1)//2;
       0 -mre*(sre5+1)//2 mre;
       0 -mre*(sre5+1)//2 -mre;
       (1+sre5)//4 mre*(sre5+3)//4 mre;
       (1+sre5)//4 mre*(sre5+3)//4 -mre;
       -(1+sre5)//4 mre*(sre5+3)//4 mre;
       -(1+sre5)//4 mre*(sre5+3)//4 -mre;
       (3+sre5)//4 -mre//2 mre;
       (3+sre5)//4 -mre//2 -mre;
       -(3+sre5)//4 -mre//2 mre;
       -(3+sre5)//4 -mre//2 -mre;
       1//2 mre*(sre5+5)//4 0;
       1//2 -mre*(sre5+5)//4 0;
       -1//2 mre*(sre5+5)//4 0;
       -1//2 -mre*(sre5+5)//4 0;
       (3+sre5)//4 sre5*mre//2 0;
       (3+sre5)//4 -sre5*mre//2 0;
       -(3+sre5)//4 sre5*mre//2 0;
       -(3+sre5)//4 -sre5*mre//2 0;
       (1+sre5)//2 0 0;
       -(1+sre5)//2 0 0]
  return convex_hull(EMF, V; non_redundant = true)
end

function _johnson_solid(::Val{35})
  Qx, x = QQ["x"]
  NF, srv = number_field([x^2 - 2, x^2 - 3])
  ENF, srev = Hecke.embedded_field(NF, real_embeddings(NF)[4])
  sre2, sre3 = srev
  V = [1//2 sre3//2 1//2;
       1//2 sre3//2 -1//2;
       1//2 -sre3//2 1//2;
       1//2 -sre3//2 -1//2;
       -1//2 sre3//2 1//2;
       -1//2 sre3//2 -1//2;
       -1//2 -sre3//2 1//2;
       -1//2 -sre3//2 -1//2;
       1 0 1//2;
       1 0 -1//2;
       -1 0 1//2;
       -1 0 -1//2;
       1//2 -sre3//6 (3+2*sre2*sre3)//6;
       1//2 -sre3//6 -(3+2*sre2*sre3)//6;
       -1//2 -sre3//6 (3+2*sre2*sre3)//6;
       -1//2 -sre3//6 -(3+2*sre2*sre3)//6;
       0 sre3//3 (3+2*sre2*sre3)//6;
       0 sre3//3 -(3+2*sre2*sre3)//6]
  return convex_hull(ENF, V; non_redundant = true)
end

function _johnson_solid(::Val{36})
  Qx, x = QQ["x"]
  NF, srv = number_field([x^2 - 2, x^2 - 3])
  ENF, srev = Hecke.embedded_field(NF, real_embeddings(NF)[4])
  sre2, sre3 = srev
  V = [1//2 sre3//2 1//2;
       1//2 sre3//2 -1//2;
       1//2 -sre3//2 1//2;
       1//2 -sre3//2 -1//2;
       -1//2 sre3//2 1//2;
       -1//2 sre3//2 -1//2;
       -1//2 -sre3//2 1//2;
       -1//2 -sre3//2 -1//2;
       1 0 1//2;
       1 0 -1//2;
       -1 0 1//2;
       -1 0 -1//2;
       1//2 -sre3//6 (3+2*sre2*sre3)//6;
       1//2 sre3//6 -(3+2*sre2*sre3)//6;
       -1//2 -sre3//6 (3+2*sre2*sre3)//6;
       -1//2 sre3//6 -(3+2*sre2*sre3)//6;
       0 sre3//3 (3+2*sre2*sre3)//6;
       0 -sre3//3 -(3+2*sre2*sre3)//6]
  return convex_hull(ENF, V; non_redundant = true)
end

function _johnson_solid(::Val{38})
  Qx, x = QQ["x"]
  NF, sr5 = number_field(x^2 - 5)
  NFy, y = NF["y"]
  MF, mr = number_field(y^2 - (5 + sr5)//10)
  EMF, mre = Hecke.embedded_field(MF, real_embeddings(MF)[4])
  sre5 = EMF(sr5)
  V = [1//2 mre*(sre5+5)//4 1//2;
       1//2 mre*(sre5+5)//4 -1//2;
       1//2 -mre*(sre5+5)//4 1//2;
       1//2 -mre*(sre5+5)//4 -1//2;
       -1//2 mre*(sre5+5)//4 1//2;
       -1//2 mre*(sre5+5)//4 -1//2;
       -1//2 -mre*(sre5+5)//4 1//2;
       -1//2 -mre*(sre5+5)//4 -1//2;
       (3+sre5)//4 sre5*mre//2 1//2;
       (3+sre5)//4 sre5*mre//2 -1//2;
       (3+sre5)//4 -sre5*mre//2 1//2;
       (3+sre5)//4 -sre5*mre//2 -1//2;
       -(3+sre5)//4 sre5*mre//2 1//2;
       -(3+sre5)//4 sre5*mre//2 -1//2;
       -(3+sre5)//4 -sre5*mre//2 1//2;
       -(3+sre5)//4 -sre5*mre//2 -1//2;
       (1+sre5)//2 0 1//2;
       (1+sre5)//2 0 -1//2;
       -(1+sre5)//2 0 1//2;
       -(1+sre5)//2 0 -1//2;
       1//2 -mre*(sre5+1)//4 (1+mre*(sre5-1))//2;
       1//2 -mre*(sre5+1)//4 -(1+mre*(sre5-1))//2;
       -1//2 -mre*(sre5+1)//4 (1+mre*(sre5-1))//2;
       -1//2 -mre*(sre5+1)//4 -(1+mre*(sre5-1))//2;
       (1+sre5)//4 mre*(sre5-1)//4 (1+mre*(sre5-1))//2;
       (1+sre5)//4 mre*(sre5-1)//4 -(1+mre*(sre5-1))//2;
       -(1+sre5)//4 mre*(sre5-1)//4 (1+mre*(sre5-1))//2;
       -(1+sre5)//4 mre*(sre5-1)//4 -(1+mre*(sre5-1))//2;
       0 mre (1+mre*(sre5-1))//2;
       0 mre -(1+mre*(sre5-1))//2]
  return convex_hull(EMF, V; non_redundant = true)
end

function _johnson_solid(::Val{39})
  Qx, x = QQ["x"]
  NF, sr5 = number_field(x^2 - 5)
  NFy, y = NF["y"]
  MF, mr = number_field(y^2 - (5 + sr5)//10)
  EMF, mre = Hecke.embedded_field(MF, real_embeddings(MF)[4])
  sre5 = EMF(sr5)
  V = [1//2 mre*(sre5+5)//4 1//2;
       1//2 mre*(sre5+5)//4 -1//2;
       1//2 -mre*(sre5+5)//4 1//2;
       1//2 -mre*(sre5+5)//4 -1//2;
       -1//2 mre*(sre5+5)//4 1//2;
       -1//2 mre*(sre5+5)//4 -1//2;
       -1//2 -mre*(sre5+5)//4 1//2;
       -1//2 -mre*(sre5+5)//4 -1//2;
       (3+sre5)//4 sre5*mre//2 1//2;
       (3+sre5)//4 sre5*mre//2 -1//2;
       (3+sre5)//4 -sre5*mre//2 1//2;
       (3+sre5)//4 -sre5*mre//2 -1//2;
       -(3+sre5)//4 sre5*mre//2 1//2;
       -(3+sre5)//4 sre5*mre//2 -1//2;
       -(3+sre5)//4 -sre5*mre//2 1//2;
       -(3+sre5)//4 -sre5*mre//2 -1//2;
       (1+sre5)//2 0 1//2;
       (1+sre5)//2 0 -1//2;
       -(1+sre5)//2 0 1//2;
       -(1+sre5)//2 0 -1//2;
       1//2 -mre*(sre5+1)//4 (1+mre*(sre5-1))//2;
       -1//2 -mre*(sre5+1)//4 (1+mre*(sre5-1))//2;
       -1//2 mre*(sre5+1)//4 -(1+mre*(sre5-1))//2;
       1//2 mre*(sre5+1)//4 -(1+mre*(sre5-1))//2;
       (1+sre5)//4 mre*(sre5-1)//4 (1+mre*(sre5-1))//2;
       -(1+sre5)//4 mre*(sre5-1)//4 (1+mre*(sre5-1))//2;
       -(1+sre5)//4 -mre*(sre5-1)//4 -(1+mre*(sre5-1))//2;
       (1+sre5)//4 -mre*(sre5-1)//4 -(1+mre*(sre5-1))//2;
       0 mre (1+mre*(sre5-1))//2;
       0 -mre -(1+mre*(sre5-1))//2]
  return convex_hull(EMF, V; non_redundant = true)
end



# function _johnson_solid(::Val{87})
#   Qx, x = QQ["x"]
#   NF, ks = number_field(60*x^4 - 48*x^3 - 100*x^2 + 56*x + 23)
#   NFy, y = NF["y"]
#   UNF, us = number_field(y^2 - 1 + ks^2)
#   ENF, u = Hecke.embedded_field(UNF, real_embeddings(UNF)[4])
#   k = ENF(ks) 
#   v = (-13//27*k^3 - 208//135*k^2 + 1733//810*k + 449//405)*u
#   w = (4//27*k^3 + 64//135*k^2 + 668//405*k - 512//405)*u
# end

function _johnson_solid(::Val{88})
  Qx, x = QQ["x"]
  NF, ks = number_field(1680*x^16- 4800*x^15 - 3712*x^14 + 17216*x^13+ 1568*x^12 - 24576*x^11 + 2464*x^10 + 17248*x^9- 3384*x^8 - 5584*x^7 + 2000*x^6+ 240*x^5- 776*x^4+ 304*x^3 + 200*x^2 - 56*x - 23)
  NFy, y = NF["y"]
  UNF, us = number_field(y^2 - 1 + ks^2)
  ENF, u = Hecke.embedded_field(UNF, real_embeddings(UNF)[4])
  k = ENF(ks) 
  v = (-779398396//3645*k^15 + 1527897016//3645*k^14 + 47481585556//54675*k^13 - 80358097444//54675*k^12 - 626829326//405*k^11 + 34715953556//18225*k^10 + 15225336298//10935*k^9 - 61415739374//54675*k^8 - 30047329289//54675*k^7 + 16348591376//54675*k^6 - 128888737//18225*k^5 - 282199511//6075*k^4 + 7240761619//109350*k^3 + 925235176//54675*k^2 - 1435429847//109350*k - 404623837//109350)*u
  w = (-4937536//3645*k^15 + 66072592//25515*k^14 + 1900033672//382725*k^13 - 429863104//54675*k^12 - 3078356//405*k^11 + 1002736772//127575*k^10 + 408983716//76545*k^9 - 1127158988//382725*k^8 - 481084868//382725*k^7 + 137102912//382725*k^6 - 37465594//127575*k^5 - 5910032//42525*k^4 + 59708339//382725*k^3 + 3939991//54675*k^2 - 4189357//382725*k - 2877197//382725)*u
  V = [0 1//2 u; 
      0 -1//2 u; 
      k 1//2 0;
      k -1//2 0;
      -k 1//2 0;
      -k -1//2 0;
      0 w//(2*u)+1//2 (1-2*k^2)//(2*u);
      0 -w//(2*u)-1//2 (1-2*k^2)//(2*u);
      1//2 0 -v//2;
      -1//2 0 -v//2;
      0 w*(2*k^2-1)//(2*(k^2-1)*u)+1//2 (2*k^4-1)//(2*u^3);
      0 -w*(2*k^2-1)//(2*(k^2-1)*u)-1//2 (2*k^4-1)//(2*u^3)]
  return convex_hull(ENF, V; non_redundant = false)
end

function _johnson_solid(::Val{89})
  Qx, x = QQ["x"]
  NF, ks = number_field(26880*x^10 + 35328*x^9 - 25600*x^8 - 39680*x^7 + 6112x^6 + 13696*x^5 + 2128*x^4 - 1808*x^3 - 1119*x^2 + 494*x - 47)
  NFy, y = NF["y"]
  UNF, us = number_field(y^2 - 1 + ks^2)
  ENF, u = Hecke.embedded_field(UNF, real_embeddings(UNF)[6])
  k = ENF(ks) 
  v = (-174265//72*k^9 - 263299//72*k^8 + 354083//216*k^7 + 213419//54*k^6 + 333139//1728*k^5 - 2134337//1728*k^4 - 1505857//3456*k^3 + 147085//1728*k^2 + 6787789//55296*k - 1258781//55296)*u
  w = (-340207525//80208*k^9 - 524173255//80208*k^8 + 621900263//240624*k^7 + 411287453//60156*k^6 + 1019406967//1924992*k^5 - 3914171453//1924992*k^4 - 2949983917//3849984*k^3 + 217946413//1924992*k^2 + 12238010281//61599744*k - 2178441785//61599744)*u
  V = [1//2 1//2 u;
      1//2 -1//2 u;
      -1//2 1//2 u;
      -1//2 -1//2 u;
      1//2+k 1//2 0;
      1//2+k -1//2 0;
      -1//2-k 1//2 0;
      -1//2-k -1//2 0;
      1//2 0 -w//2;
      -1//2 0 -w//2;
      0 1//2+v//(2*u) v^2//(4*u);
      0 -1//2-v//(2*u) v^2//(4*u);
      0 (v*w+k+1)//(4*u^2) (2*k-1)*w//(4*(1-k))-v//(4*u^2);
      0 -(v*w+k+1)//(4*u^2) (2*k-1)*w//(4*(1-k))-v//(4*u^2)]
  return convex_hull(ENF, V; non_redundant = true)
end

function _johnson_solid(::Val{90})
  Qx, x = QQ["x"]
  NF, ks = number_field(256*x^12 - 512*x^11 - 1664*x^10 + 3712*x^9 + 1552*x^8 - 6592*x^7 + 1248*x^6 + 4352*x^5 - 2024*x^4 - 944*x^3 + 672*x^2 - 24*x - 23)
  NFy, y = NF["y"]
  UNF, us = number_field(y^2 - 1 + ks^2)
  ENF, u = Hecke.embedded_field(UNF, real_embeddings(UNF)[6])
  k = ENF(ks) 
  v = (-12736//405*k^11 + 17728//405*k^10 + 32512//135*k^9 - 131488//405*k^8 - 184124//405*k^7 + 259436//405*k^6 + 125426//405*k^5 - 23542//45*k^4 - 13363//405*k^3 + 66277//405*k^2 - 17923//810*k - 5449//810)*u
  w = (-22592//405*k^11 + 28256//405*k^10 + 55664//135*k^9 - 200696//405*k^8 - 281488//405*k^7 + 360832//405*k^6 + 157612//405*k^5 - 28904//45*k^4 - 15476//405*k^3 + 72974//405*k^2 - 6898//405*k - 7073//810)*u
  V =  [1//2 0 u+v//4; 
        -1//2 0 u+v//4; 
        0 1//2 -u-v//4; 
        0 -1//2 -u-v//4;
        1//2+w//(2*u) 0 u-1//(2*u)+v//4;
        -1//2-w//(2*u) 0 u-1//(2*u)+v//4;
        0 1//2+w//(2*u) -u+1//(2*u)-v//4;
        0 -1//2-w//(2*u) -u+1//(2*u)-v//4;
        1//2 k v//4; 
        1//2 -k v//4;
        -1//2 k v//4; 
        -1//2 -k v//4;
        k 1//2 -v//4; 
        -k 1//2 -v//4;
        k -1//2 -v//4; 
        -k -1//2 -v//4]
  return convex_hull(ENF, V; non_redundant = true)
end

function _johnson_solid(::Val{92})
  Qx, x = QQ["x"]
  NF, srs = number_field([x^2 - 3, x^2 - 5])
  ENF, srse = Hecke.embedded_field(NF, real_embeddings(NF)[4])
  sr3, sr5 = srse
  V = [1//2 -sr3//6 sr3*(3+sr5)//6;
       -1//2 -sr3//6 sr3*(3+sr5)//6;
       0 sr3//3 sr3*(3+sr5)//6;
       1//2 sr3*(2+sr5)//6 sr3*(1+sr5)//6;
       -1//2 sr3*(2+sr5)//6 sr3*(1+sr5)//6;
       (3+sr5)//4 -sr3*(sr5-1)//12 sr3*(1+sr5)//6;
       -(3+sr5)//4 -sr3*(sr5-1)//12 sr3*(1+sr5)//6;
       (1+sr5)//4 -sr3*(5+sr5)//12 sr3*(1+sr5)//6;
       -(1+sr5)//4 -sr3*(5+sr5)//12 sr3*(1+sr5)//6;
       (3+sr5)//4 sr3*(3+sr5)//12 sr3//3;
       -(3+sr5)//4 sr3*(3+sr5)//12 sr3//3;
       0 -sr3*(3+sr5)//6 sr3//3; 
       1//2 sr3//2 0;
       1//2 -sr3//2 0;
       -1//2 sr3//2 0;
       -1//2 -sr3//2 0;
       1 0 0; 
       -1 0 0]
  return convex_hull(ENF, V; non_redundant = true)
end

