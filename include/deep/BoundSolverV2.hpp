#ifndef BOUND_SOLVER_V2_HPP
#define BOUND_SOLVER_V2_HPP

#include "BoundSolver.hpp" 
#include "RndLearnerV4.hpp"

namespace ufo {
  class BoundSolverV2 : public BoundSolver {
  private:
    ExprMap bounds;
    Expr fcBodyOrig;
    int n; // parameter to control the number of trace iterations.
    int limit;

    int to = 50;
    int freqs = 1;
    int aggp = 1;
    int mut = 2;
    int dat = 1;
    int doProp = 0;
    int mutData = 1;
    bool doDisj = true;
    bool mbpEqs = false;
    bool dAllMbp = false;
    bool dAddProp = false;
    bool dAddDat = true;
    bool dStrenMbp = false;
    bool dFwd = false;
    bool dRec = false;
    bool dGenerous = false;

    bool doGJ = false;
    bool doConnect = false;
    bool absConsts = false;
    bool dataInfer = false;
    bool imp = false;
    bool mutateInferred = false;
    bool sepOps = false;
    bool checkProj = false;

    ExprMap abstrVars;
    string abdstrName = "_AB_";

  public:
    BoundSolverV2(CHCs &r, int _b, bool _dg, bool d2, bool _dp, int _limit, bool gj,
                  bool dc, bool abConsts, bool iwd, bool _imp, bool mi, bool _sepOps,
                  bool _tk, int md, int dbg)
        : BoundSolver(r, _b, _dg, d2, _dp, dbg), limit(_limit), n(_limit), doGJ(gj),
          doConnect(dc), absConsts(abConsts), dataInfer(iwd), imp(_imp),
          mutateInferred(mi), sepOps(_sepOps), checkProj(_tk), mutData(md)
    {
      if(absConsts) abstractConsts(); 
      
      for(auto& chc: r.chcs) 
      {
        if(chc.isFact)
        {
          fcBodyOrig = chc.body;
          if(debug >= 6) outs() << "fcBodyOrig: " << fcBodyOrig << "\n";
        }
      }
      for (auto & a : ruleManager.chcs)
        if (a.isInductive) tr = &a;
        else if (a.isQuery) qr = &a;
        else fc = &a;
        
      tr_orig = *tr;

      fc_nogh = *fc;
      tr_nogh = *tr;
      qr_nogh = *qr;
      removeQuery();
    }

    void abstractConst(Expr e, HornRuleExt& hr)
    {
      int val = lexical_cast<int>(e);
      if(debug >= 5) outs() << val << " <= " << limit << "?\n";
      if(val <= limit) return;

      if(debug >= 5)
      {
        outs() << "Abstract a constant: ";
        outs() << "e: " << e << "\n";
        outs() << "e->arg(i): " << typeOf(e) << "\n";
        outs() << std::endl;
      }

      // Check each set of pairs to see if they can be related.
      // ex. 10000, 5000, 2000. 

      Expr var;
      Expr varPr;
      Expr type = typeOf(e);
      for(auto& av: abstrVars)
      {
        if(av.second == e)
        {
          var = fapp(constDecl(av.first, type));
          if(debug >= 4) outs() << "Constant already abstracted: " << var << "\n";
          hr.body = replaceAll(hr.body, e, var);
          return;
        }

        cpp_int eVal = lexical_cast<cpp_int>(e);
        cpp_int avVal = lexical_cast<cpp_int>(av.second);
        if(avVal % eVal == 0)
        {
          cpp_int div = avVal / eVal;
          var = mk<MULT>(mkMPZ(div, m_efac), av.first);
          if (debug >= 4)
            outs() << "Constant already abstracted: " << var << "\n";
          hr.body = replaceAll(hr.body, av.first, var);
          hr.body = replaceAll(hr.body, e, av.first);
          av.second = e;
          return;
        }
        else if (eVal % avVal == 0)
        {
          cpp_int div = eVal / avVal;
          var = mk<MULT>(mkMPZ(div, m_efac), av.first);
          if (debug >= 4)
            outs() << "Constant already abstracted: " << var << "\n";
          hr.body = replaceAll(hr.body, av.first, var);
          hr.body = replaceAll(hr.body, e, av.first);
          av.second = e;

          return;
        }
        else
        {
          outs() << "Unable to find relationships between " << eVal << " and " << avVal << "\n";
        }
      }
      var = mkTerm<string>("_AB_" + lexical_cast<string>(abstrVars.size()), m_efac);
      var = fapp(constDecl(var, type));
      varPr = mkTerm<string>("_AB_" + lexical_cast<string>(abstrVars.size()) + "'", m_efac);
      varPr = fapp(constDecl(varPr, type));
      abstrVars[var] = e;
      if (debug >= 4)
        outs() << "var: " << var << "\n";
      hr.body = replaceAll(hr.body, e, var);
      if (debug >= 4)
        outs() << "hr.body: " << hr.body << "\n";
    }

    void findIte(Expr& rhs, HornRuleExt& hr)
    {
      if(isOpX<ITE>(rhs))
      {
        Expr cond = rhs->left();
        Expr then = rhs->arg(1);
        Expr els = rhs->arg(2);
        if (debug >= 4)
          outs() << "rhs: " << rhs << "\n";
        if (debug >= 4)
          outs() << "cond: " << cond << "\n";
        if (debug >= 4)
          outs() << "then: " << then << "\n";
        if (debug >= 4)
          outs() << "els: " << els << "\n";

        if(isOpX<ITE>(then))
        {
          findIte(then, hr);
        }
        if(isOpX<ITE>(els))
        {
          findIte(els, hr);
        }

        if(isNumericConst(cond->right()))
        {
          abstractConst(cond->right(), hr);
        }
      }
      else if(containsOp<ITE>(rhs))
      {
        Expr lhs = rhs->left();
        Expr rhs2 = rhs->right();
        if(debug >= 4) outs() << "lhs: " << lhs << "\n";
        if(debug >= 4) outs() << "rhs2: " << rhs2 << "\n";
        if(lhs != NULL && containsOp<ITE>(lhs)) findIte(lhs, hr);
        if(rhs2 != NULL && containsOp<ITE>(rhs2)) findIte(rhs2, hr);
      }
    }

    Expr abstractPreCond()
    {
      // Add a precond on the new abtract var.
      if(debug >= 5)
      {
        for(auto& a: abstrVars)
        {
          outs() << "abstractVars: " << a.first << " --> " << a.second << "\n";
        }
      }

      ExprSet preConds;
      for(auto& av: abstrVars)
      {
        if(lexical_cast<int>(av.second) > 0)
          preConds.insert(replaceAll(mk<GT>(av.first, mpzZero), tr->srcVars, fc->dstVars));
        if(lexical_cast<int>(av.second) < 0)
          preConds.insert(replaceAll(mk<LT>(av.first, mpzZero), tr->srcVars, fc->dstVars));

        for(auto& av2: abstrVars)
        {
          if(av2 == av) continue;
          if(lexical_cast<int>(av.second) > lexical_cast<int>(av2.second))
            preConds.insert(replaceAll(mk<GT>(av.first, av2.first), tr->srcVars, fc->dstVars));
          if(lexical_cast<int>(av.second) < lexical_cast<int>(av2.second))
            preConds.insert(replaceAll(mk<LT>(av.first, av2.first), tr->srcVars, fc->dstVars));
        }
      }

      return conjoin(preConds, m_efac);
    }

    void abstractConsts() // Look for large numerical values and abstract them to a variable.
    {
      // Find values.
      for(auto& hr: ruleManager.chcs)
      {
        ExprVector conjs;
        getConj(hr.body, conjs);
        for(auto& c: conjs)
        {
          if(debug >= 4) outs() << "conj: " << c << "\n";
          ExprVector vars;
          filter(c, IsConst(), inserter(vars, vars.begin()));
          Expr rhs = c->right();
          Expr lhs = c->left();
          if(isNumericConst(rhs))
          {
            abstractConst(rhs, hr);
          }
          if(isNumericConst(lhs))
          {
            abstractConst(lhs, hr);
          }
          if(containsOp<ITE>(rhs))
          {
            if(debug >= 4) outs() << "HAS ITE\n";
            if(debug >= 4) outs() << "rhsITE: " << rhs << "\n";
            findIte(rhs, hr);
          }
        }
      }
      
      for(auto& hr: ruleManager.chcs)
      {
        for(auto& av: abstrVars)
        {
          if(hr.srcRelation != mk<TRUE>(m_efac))
          {
            if(debug >= 4) outs() << "av1: " << av.first << "\n";
            if(debug >= 4) outs() << "av2: " << av.second << "\n";
            hr.srcVars.push_back(av.first);
          }
          Expr dstVar = mkTerm<string>(lexical_cast<string>(av.first) + "'", m_efac);
          dstVar = fapp(constDecl(dstVar, typeOf(av.second)));
          if(!hr.isQuery) hr.dstVars.push_back(dstVar);

          if(hr.isInductive)
          {
            hr.body = mk<AND>(hr.body, mk<EQ>(av.first, dstVar));
          }
        }
        if (debug >= 4)
        {
          outs() << "Vars for " << hr.srcRelation << ": ";
          for(auto& v: hr.srcVars)
          {
            outs() << v << " ";
          }
          outs() << "\n";
        }
      }

      for(auto& hr: ruleManager.chcs)
      {
        if(hr.isFact)
        {
          hr.body = mk<AND>(hr.body, abstractPreCond());
        }
      }

      if(debug >= 4)
      {
        outs() << "\n** NEW CHCS **\n";
        ruleManager.print(true);
      } 
    }

    void copyRule(HornRuleExt* dst, HornRuleExt* src)
    {
      dst->srcRelation = src->srcRelation;
      dst->dstRelation = src->dstRelation;
      dst->srcVars = src->srcVars;
      dst->dstVars = src->dstVars;
      dst->body = src->body;
      dst->isFact = src->isFact;
      dst->isQuery = src->isQuery;
      dst->isInductive = src->isInductive;
    }

    void prepareRuleManager(CHCs& rm, vector<HornRuleExt*>& rules)
    {
      rm.addFailDecl(ruleManager.failDecl);

      for (auto &r : rules)
      {
        rm.addRule(r);
      }
      rm.findCycles();

      rm.dwtoCHCs = rm.wtoCHCs;
      for (auto it = rm.dwtoCHCs.begin(); it != rm.dwtoCHCs.end();)
        if ((*it)->isQuery) it = rm.dwtoCHCs.erase(it);
          else ++it;

      if(debug >= 4) rm.print(true);
    }

    Expr setGhostGuard(Expr value)
    {
      return mk<EQ>(ghostVars[0],value);
    }

    void prepareRulesWithPrecond(Expr elim, Expr preCond, CHCs& rm)
    {
      HornRuleExt* fcWithPrecond = new HornRuleExt();
      copyRule(fcWithPrecond, fc);
      fcWithPrecond->isFact = true;
      fcWithPrecond->srcRelation = mk<TRUE>(m_efac);
      Expr fcPreCond = replaceAll(elim, tr->srcVars, fc->srcVars);
      Expr body = replaceAll(fcWithPrecond->body, fcWithPrecond->srcVars, tr->dstVars);
      body = u.removeRedundantConjuncts(body);
      fcPreCond = replaceAll(mk<AND>(fcPreCond, normalize(preCond), body), fcWithPrecond->srcVars, tr->dstVars);
      if (debug >= 3) outs() << "Original fcBody: " << fcWithPrecond->body << "\n";
      fcWithPrecond->body = fcPreCond;
      fcWithPrecond->srcVars.clear();

      ExprVector qrBody;
      getConj(qr->body, qrBody);
      for (auto c = qrBody.begin(); c != qrBody.end(); )
      {
        if (contains(*c, ghostVars[0])) c = qrBody.erase(c);
        else ++c;
      }
      
      qrBody.push_back(mkNeg(ghostGuard));
      HornRuleExt* qrForFH = new HornRuleExt();
      copyRule(qrForFH, qr);
      qrForFH->body = conjoin(qrBody, m_efac);

      vector<HornRuleExt*> rules;
      rules.push_back(fcWithPrecond);
      rules.push_back(tr);
      rules.push_back(qrForFH);
      prepareRuleManager(rm, rules);
    }

    void mutateHeuristicEq(ExprSet &src, ExprSet &dst)
    {
      ExprSet src2;
      map<Expr, ExprVector> substs;
      Expr (*ops[])(Expr, Expr) = {mk<PLUS>, mk<MINUS>}; // operators used in the mutations

      for (auto a1 = src.begin(); a1 != src.end(); ++a1)
        if (isNumericEq(*a1) && contains(*a1, ghostVars[0]))
        {
          for (auto a2 = std::next(a1); a2 != src.end(); ++a2) // create various combinations
            if (isNumericEq(*a2) && !contains(*a2, ghostVars[0]))
            {
              const ExprVector m1[] = {{(*a1)->left(), (*a2)->left()}, {(*a1)->left(), (*a2)->right()}};
              const ExprVector m2[] = {{(*a1)->right(), (*a2)->right()}, {(*a1)->right(), (*a2)->left()}};
              for (int i : {0, 1})
                for (Expr (*op)(Expr, Expr) : ops)
                  src2.insert(simplifyArithm(normalize(
                      mk<EQ>((*op)(m1[i][0], m1[i][1]), (*op)(m2[i][0], m2[i][1])))));
            }

          // before pushing them to the cand set, we do some small mutations to get rid of specific consts
          Expr a = simplifyArithm(normalize(*a1));
          if (isOpX<EQ>(a) && isIntConst(a->left()) &&
              isNumericConst(a->right()) && lexical_cast<string>(a->right()) != "0")
            substs[a->right()].push_back(a->left());
          src2.insert(a);
        }

      bool printedAny = false;
      if (debug >= 2)
        outs() << "Mutated candidates:\n";
      for (auto a : src2)
        if (!u.isFalse(a) && !u.isTrue(a))
        {
          if (debug >= 2)
          {
            outs() << "  " << a << "\n";
            printedAny = true;
          }

          dst.insert(a);

          if (isNumericConst(a->right()))
          {
            cpp_int i1 = lexical_cast<cpp_int>(a->right());
            for (auto b : substs)
            {
              cpp_int i2 = lexical_cast<cpp_int>(b.first);

              if (i1 % i2 == 0 && i1 / i2 != 0)
                for (auto c : b.second)
                {
                  Expr e = simplifyArithm(normalize(mk<EQ>(a->left(), mk<MULT>(mkMPZ(i1 / i2, m_efac), c))));
                  if (!u.isSat(mk<NEG>(e)))
                    continue;

                    dst.insert(e);

                  if (debug >= 2)
                  {
                    outs() << "  " << e << "\n";
                    printedAny = true;
                  }
                }
            }
          }
        }
      if (debug >= 2 && !printedAny)
        outs() << "  none\n";
    }

    ExprSet prevInvs;
    boost::tribool checkSafety(Expr elim, Expr preCond)
    {

      if(debug >= 2) outs() << "\n\nCheck Safety\n============\n";
      if(debug >= 3)
      {
        outs() << "  precond: " << elim << "\n";
        outs() << "  bound: " << preCond << "\n";
      }
      if(!u.isSat(elim))
      {
        if(debug >= 3) outs() << "  elim is unsat.\n";
        return false;
      }
      // add precondition to be checked to the ruleManager.
      CHCs rm(m_efac, z3, debug);

      prepareRulesWithPrecond(elim, preCond, rm);

      BndExpl bnd(rm, to, debug);
      RndLearnerV4 ds(m_efac, z3, rm, to, freqs, aggp, mut, dat,
                      doDisj, mbpEqs, dAllMbp, dAddProp, dAddDat, dStrenMbp,
                      dFwd, dRec, dGenerous, (debug >= 6 ? 2 : 0));

      map<Expr, ExprSet> cands;
      for (auto &cyc : rm.cycles)
      {
        Expr rel = cyc.first;
        for (int i = 0; i < cyc.second.size(); i++)
        {
          Expr dcl = rm.chcs[cyc.second[i][0]].srcRelation;
          if (ds.initializedDecl(dcl))
            continue;
          ds.initializeDecl(dcl);
          Expr pref = bnd.compactPrefix(rel, i);
          ExprSet tmp;
          getConj(pref, tmp);
          for (auto &t : tmp)
            if (hasOnlyVars(t, rm.invVars[dcl]))
              cands[dcl].insert(t);
          if (mut > 0)
            ds.mutateHeuristicEq(cands[dcl], cands[dcl], dcl, true);
          ds.initializeAux(cands[dcl], bnd, rel, i, pref);
        }
      }
      if (dat > 0)
        ds.getDataCandidates(cands);
      for (auto &dcl : rm.wtoDecls)
      {
        for (int i = 0; i < doProp; i++)
          for (auto &a : cands[dcl])
            ds.propagate(dcl, a, true);
        ds.addCandidates(dcl, cands[dcl]);
        ds.prepareSeeds(dcl, cands[dcl]);
      }
      for (auto &dcl : rm.decls)
      {
        ds.addCandidates(dcl, cands[dcl]);
      }
      ds.addCandidates(invDecl, prevInvs);
      if(ds.bootstrap())
      { 
        return true;
      }
      ds.calculateStatistics();
      ds.deferredPriorities();
      std::srand(std::time(0));
      boost::tribool res = ds.synthesize(to);

      if(res)
      {
        prevInvs = ds.getlearnedLemmas(0);
      }

      return res;
    }

    void removeCommonExpr(ExprVector &d, ExprVector& toDisj, Expr& cm)
    {
      if (d.size() <= 1)
      {
        toDisj = d;
        cm = mk<TRUE>(m_efac);
        return;
      }

      ExprSet comm;
      vector<ExprSet> dsjs;
      dsjs.push_back(ExprSet());
      auto it = d.begin();
      getConj(*it, dsjs.back());
      comm = dsjs.back();
      for (it = std::next(it); it != d.end(); ++it)
      {
        ExprSet updComm, tmp;
        dsjs.push_back(ExprSet());
        getConj(*it, dsjs.back());
        tmp = dsjs.back();
        distribDisjoin(comm, tmp, updComm);
        comm = updComm;
      }

      for (auto a : dsjs)
      {
        minusSets(a, comm);
        toDisj.push_back(normalize(conjoin(a, m_efac)));
      }
      
      u.removeRedundantConjuncts(comm);
      cm = conjoin(comm, m_efac);
    }

    void splitExprs(ExprVector& BigPhi, map<Expr,ExprVector>& infMap)
    {
      if(debug >= 3) outs() << "\nSplit Exprs\n===========\n";

      for(auto& cc: BigPhi)
      {
        Expr c = normalize(cc, true);
        if(debug >= 4) outs() << "Splitting: " << c << "\n";
        ExprVector lhs;
        getConj(c, lhs); // handle Disjuncts.
        for(int i = 0; i < lhs.size(); i++)
        {
          Expr lhsi = lhs[i]->left();
          infMap[lhsi].push_back(lhs[i]);
        }
      }
    }

    void filterBigPhi(ExprVector& BigPhi)
    {
      ExprVector temp;
      for (auto &c : BigPhi)
      {
        c = normalize(c, true);
        if (debug >= 4)
          outs() << "  c: " << c << "\n";
        ExprSet conjs;
        getConj(c, conjs);
        ExprVector vars;
        Expr toChange;
        Expr conj;
        for (auto &t : conjs)
        {
          if (t->left()->arity() == 1)
          {
            toChange = t->right();
            conj = t;
            filter(t, IsConst(), inserter(vars, vars.begin()));
          }
        }
        for (auto &t : conjs)
        {
          if (!vars.empty() && t->left()->arity() > 1 && contains(t, vars[0]))
          {
            ExprSet tmp;
            getConj(t, tmp);
            for (auto &tt : tmp)
            {
              if (contains(tt, vars[0]))
              {
                Expr ttt = tt;
                ttt = simplifyArithm(replaceAll(ttt, vars[0], toChange));
                ttt = ineqReverter(ttt);
                temp.push_back(normalize(mk<AND>(ttt, conj)));
              }
            }
          }
        }
      }
      if(!temp.empty()) BigPhi = temp;
    }

    Expr getLinComb(Expr eq, Expr inEq, double eqConst, double inEqConst)
    {
      if (debug >= 5)
      {
        outs() << "Processing linear combination\n";
        outs() << "eq: " << *eq << "\n";
        outs() << "inEq: " << *inEq << "\n";
        outs() << "eqConst: " << eqConst << "\n";
        outs() << "inEqConst: " << inEqConst << "\n";
      }

      Expr e = mk<TRUE>(m_efac);
      if ((isOpX<GEQ>(inEq) || isOpX<GT>(inEq)) && inEqConst > eqConst)
      {
        e = mk<GT>(inEq->left(), eq->left());
      }
      else if ((isOpX<LEQ>(inEq) || isOpX<LT>(inEq)) && inEqConst < eqConst)
      {
        e = mk<LT>(inEq->left(), eq->left());
      }
      else if ((isOpX<GEQ>(inEq) || isOpX<GT>(inEq)) && inEqConst < eqConst)
      {
        e = mk<GEQ>(inEq->left(), eq->left());
      }
      else if ((isOpX<LEQ>(inEq) || isOpX<LT>(inEq)) && inEqConst > eqConst)
      {
        e = mk<LEQ>(inEq->left(), eq->left());
      }
      else if ((isOpX<GEQ>(inEq) || isOpX<GT>(inEq)) && inEqConst >= eqConst)
      {
        e = mk<GEQ>(inEq->left(), eq->left());
      }
      else if ((isOpX<LEQ>(inEq) || isOpX<LT>(inEq)) && inEqConst <= eqConst)
      {
        e = mk<LEQ>(inEq->left(), eq->left());
      }
      else if ((isOpX<GEQ>(inEq) || isOpX<GT>(inEq)) && inEqConst <= eqConst)
      {
        e = mk<GT>(inEq->left(), eq->left());
      }
      else if ((isOpX<LEQ>(inEq) || isOpX<LT>(inEq)) && inEqConst >= eqConst)
      {
        e = mk<LT>(inEq->left(), eq->left());
      }
      else if (isOpX<EQ>(inEq) && inEqConst == eqConst)
      {
        e = mk<EQ>(inEq->left(), eq->left());
      }
      else if (isOpX<NEQ>(inEq) && inEqConst != eqConst)
      {
        e = mk<NEQ>(inEq->left(), eq->left());
      }
      else
      {
        if(debug >= 5) outs() << "Unhandled case\n";
      }
      e = normalize(e);
      if (debug >= 5)
        outs() << "Adding: " << *e << "\n";
      return e;
    }

    void linCombIneq(Expr srcRel, ExprVector &forms, map<Expr, ExprSet>& dc)
    {
      if (debug >= 5)
        outs() << "Processing linear combination of inequalities\n";
      ExprSet res;
      for (auto &f : forms)
      {
        Expr const1;
        ExprVector conjs;
        getConj(f, conjs);
        if (conjs.size() < 2)
          continue;
        Expr eq = mk<TRUE>(m_efac);
        Expr inEq = mk<TRUE>(m_efac);
        for (auto &c : conjs)
        {
          // get the value of the constant.
          if (debug >= 5)
            outs() << "Processing inEq/Eq: " << *c << "\n";
          if (isOpX<EQ>(c))
          {
            if (eq != mk<TRUE>(m_efac))
              inEq = c;
            else
              eq = c;
          }
          else if (!isOpX<NEQ>(c)) 
          {
            if (inEq != mk<TRUE>(m_efac))
              eq = c;
            else
              inEq = c;
          }
        }
        if (debug >= 5)
        {
          outs() << "eq: " << *eq << "\n";
          outs() << "inEq: " << *inEq << "\n";
        }

        if(eq == mk<TRUE>(m_efac) || inEq == mk<TRUE>(m_efac)) continue;
        double eqConst = lexical_cast<double>(eq->right());
        double inEqConst = lexical_cast<double>(inEq->right());

        if (eq->left() == inEq->left())
        {
          if (res.empty())
            res.insert(inEq);
          else
          {
            Expr e = *res.rbegin();
            if (u.implies(e, inEq))
            {
              res.erase(e);
              res.insert(inEq);
            }
          }
        }
        else
        {
          res.insert(getLinComb(eq, inEq, eqConst, inEqConst));
        }
      }
      if (debug >= 5)
      {
        outs() << "Adding to data candidates\n";
        for (auto &r : res)
        {
          outs() << "  " << *r << "\n";
        }
      }
      dc[srcRel].insert(res.begin(), res.end());
    }

    bool trySimplifying(ExprVector &conjs)
    {
      ExprSet similar;
      bool eraseE = false;
      bool simplified = false;
      for (auto itr = conjs.begin(); itr != conjs.end();)
      {
        Expr e = (*itr)->left();
        for (auto jtr = conjs.begin(); jtr != conjs.end();)
        {
          if (itr == jtr)
          {
            jtr++;
            continue;
          }
          if (e == (*jtr)->left())
          {
            eraseE = true;
            simplified = true;
            jtr = conjs.erase(jtr);
          }
          else
            jtr++;
        }
        if (eraseE)
        {
          eraseE = false;
          itr = conjs.erase(itr);
        }
        else
          itr++;
      }

      if (debug > 4)
      {
        outs() << "\nSimplified:\n";
        for (auto &c : conjs)
        {
          outs() << "  " << *c << "\n";
        }
      }

      return simplified;
    }

    void makeModel(Expr srcRel, ExprVector &forms1, map<Expr, ExprSet>& dc)
    {
      ExprVector vars;
      filter(forms1[0], IsConst(), inserter(vars, vars.begin()));
      // Expects normalized exprs.

      ExprVector forms;
      for (auto it = forms1.begin(); it != forms1.end(); it++)
      {
        if (debug > 0)
          outs() << "Processing: " << *it << "\n";
        ExprVector conjs;
        getConj(*it, conjs);
        if (conjs.size() > 2)
        {
          bool keepGoing = trySimplifying(conjs);
          if (!keepGoing)
            return;
          if (debug > 4)
            outs() << "Keep going after simplifying: " << *it << "\n";
        }

        forms.push_back(conjoin(conjs, m_efac));
      }

      linCombIneq(srcRel, forms, dc);

      for (auto &it : dc[srcRel])
      {
        if (debug > 0)
          outs() << "Data candidate: " << simplifyArithm(it) << "\n";
      }
    }

    ExprSet inferWithData(ExprVector BigPhi)
    {
      if(debug >= 3) outs() << "\n\nInfer With Data\n==============\n";
      filterBigPhi(BigPhi);
      if (debug >= 4)
      {
        outs() << "  Filtered BigPhi size: " << BigPhi.size() << "\n";
        for (auto &c : BigPhi)
        {
          outs() << "  Filtered From BigPhi: " << c << "\n";
        }
      }
      map<Expr, ExprSet> dc;

      makeModel(invDecl, BigPhi, dc);

      for (auto c = dc[invDecl].begin(); c != dc[invDecl].end();)
      {
        if (debug >= 4)
          outs() << "  cands: " << *c << "\n";
        if (!u.isSat(*c, tr->body))
        {
          if(debug >= 2) outs() << "  Removed: " << *c << "\n";
          c = dc[invDecl].erase(c);
        }
        else
        {
          ++c;
        }
      }

      return dc[invDecl];
    }

    // Elements in the inferred set should approximate each of the elements in ev.
    // ex. ev = { x = 1, x = 2} then infer might result in { x >= 1 }
    void infer(ExprVector& ev, ExprSet& inferred)
    {
      if (debug >= 4)
        outs() << "...Inferring...\n";
      for (int i = 0; i < ev.size(); i++)
      {
        Expr c = ev[i];
        c = simplifyArithm(c);
        c = u.removeRedundantConjuncts(c);
        if (debug >= 4)
          outs() << "  c: " << c << "\n";
        ExprVector inferSeeds;
        if(debug >= 3 && isOpX<AND>(c))
        {
          outs() << "conjunctive infer " << c << "\n";
        }

        ExprSet tmp;
        getConj(c, tmp);
        for(auto& d: tmp)
        {
          if (isOpX<EQ>(d))
          {
            inferSeeds.push_back(mk<GEQ>(d->left(), d->right()));
            inferSeeds.push_back(mk<LEQ>(d->left(), d->right()));
          }
          else if (isOpX<NEQ>(d))
          {
            inferSeeds.push_back(mk<GT>(d->left(), d->right()));
            inferSeeds.push_back(mk<LT>(d->left(), d->right()));          
          }
          else
          {
            inferSeeds.push_back(d);
          }
        }

        if (i == 0)
        {
          inferred.insert(inferSeeds.begin(), inferSeeds.end());
        }
        else
        {
          for (auto itr = inferred.begin(); itr != inferred.end(); )
          {
            if (!u.implies(c, *itr) || (imp && u.implies(*itr, c))) 
            {
              if (debug >= 4)
                outs() << "  Erasing: " << *itr << "\n";
              itr = inferred.erase(itr);
            }
            else
              itr++;
          }
        }

        if (debug >= 4)
        {
          outs() << "Current inferred:\n";
          pprint(inferred, 2);
          outs() << "\n";
        }
      }
    }

    vector<ExprVector> separateOps(ExprVector ev)
    {
      // Sometimes expressions with the same lhs
      // but different ops are grouped together.
      // This method identifies them and separates them.

      vector<ExprVector> ret;
      map<Expr, ExprVector> opMap;
      while(!ev.empty())
      {
        auto it = ev.begin();
        opMap[*it].push_back(*it);
        it = ev.erase(it);
        for(auto m = opMap.begin(); m != opMap.end(); m++)
        {
          while(it != ev.end())
          {
            if(m->first->op() == (*it)->op())
            {
              m->second.push_back(*it);
              it = ev.erase(it);
            }
            else { it++; }
            
          }
          it = ev.begin();
        }
      }

      for(auto& m: opMap)
      {
        ret.push_back(m.second);
        if(debug >= 4) 
        {
          outs() << "  OP: " << m.first->op() << "\n";
          for(auto& mm: m.second)
            outs() << "  From opMap: " << mm << "\n";
        } 
      }
      return ret;
    }

    ExprSet infer(ExprVector &BigPhi1)
    {
      // for >3 vars then do case analysis.
      // 
      if(debug >= 3) outs() << "\n\nInfer\n=====\n";
      // Break equalities into inequalities.
      // Find weakest.
      // Check that the previous expr is an overapproximation.
      // Process them in order.
      ExprSet inferredRet;
      map<Expr, ExprVector> infMap;
      ExprVector BigPhi;

      Expr common;
      if(BigPhi1.empty()) return inferredRet;
      removeCommonExpr(BigPhi1, BigPhi, common);

      // Do data learning on BigPhi.
      ExprSet inferredFromData;
      if(dataInfer) inferredFromData = inferWithData(BigPhi); // infer2

      ExprSet inferred;
      infer(BigPhi, inferred);
      inferredRet.insert(inferred.begin(), inferred.end());

      if(absConsts && false)
      {
        ExprVector reRun;
        reRun.insert(reRun.end(), inferredRet.begin(), inferredRet.end());
        inferredRet.clear();
        infer(reRun, inferredRet);
      }

      if (common != mk<TRUE>(m_efac))
      {
        ExprSet commonSet;
        getConj(common, commonSet);
        inferredRet.insert(commonSet.begin(), commonSet.end());
      }

      inferredRet.insert(inferredFromData.begin(), inferredFromData.end());

      u.removeRedundantConjuncts(inferredRet);

      if(debug >= 4) 
      {
        outs() << "Inferred after removeRedundant: ";
        outs() << conjoin(inferredRet, m_efac) << "\n";
      }

      Expr simplified = conjoin(inferredRet,m_efac);
      simplified = simplifyArithm(simplified);
      inferredRet.clear();
      getConj(simplified, inferredRet);

      if (debug >= 2)
      {
        for (auto &i : inferredRet)
        {
          outs() << "Inferred: " << i << "\n";
        }
        for (auto &i : inferredFromData)
        {
          outs() << "Inferred from data: " << i << "\n";
        }
        outs() << "Common: " << common << "\n";
      }

      return inferredRet;
    }

    void filterCandMap(map<Expr, ExprSet> &candMap, ExprVector& rowsExpr)
    {
      for (auto &r : rowsExpr)
      {
        if (debug >= 3)
          outs() << "  rowsExpr: " << r << "\n";
        for (auto itr = candMap[invDecl].begin(); itr != candMap[invDecl].end();)
        {
          if (!u.isSat(r, *itr))
          {
            if (debug >= 3)
              outs() << "  Removed: " << *itr << "\n";
            itr = candMap[invDecl].erase(itr);
          }
          else
          {
            ++itr;
          }
        }
      }
    }

    Expr firstRowExpr = mk<TRUE>(m_efac);
    ExprVector rowsExpr;
    boost::tribool invFromData(Expr src, Expr dst, Expr block, 
                               map<Expr, ExprSet>& candMap, int n) {
      
      if(debug >= 3) outs() << "\n\nInvFromData\n===========\n";
      DataLearner2 dl2(ruleManager, z3, debug);
      Expr invs = mk<TRUE>(m_efac);
      boost::tribool res = true;
      src = replaceAll(src, invVarsPr, invVars);

      src = simplifyArithm(src);
      dst = simplifyArithm(dst);
      block = simplifyArithm(block);

      if(debug >= 4) 
      {
        outs() << "  src: " << src << "\n";
        outs() << "  dst: " << dst << "\n";
        outs() << "  block: " << block << "\n";
        outs() << "  n: " << n << "\n";
      }

      if(debug >= 3) ruleManager.print(true);

      res = dl2.connectPhase(src, dst, n, invDecl, block, invs, loopGuard, doGJ, doConnect);
      if (res == true)
      {
        dl2.getDataCands(candMap[invDecl], invDecl);
      }

      dataGrds.clear();

      for(int i = 0; i < mutData; i++)
      {
        mutateHeuristicEq(candMap[invDecl], candMap[invDecl]);
      }

      filterNonGhExp(candMap[invDecl]);
      u.removeRedundantConjuncts(dataGrds);
      if (debug >= 3) 
      {
        outs() << "dataGuards: \n";
        for (auto &d : dataGrds) outs() << d << "\n";
      }

      rowsExpr = dl2.exprForRows(invDecl);
      if(rowsExpr.size() > 0) firstRowExpr = rowsExpr[0];

      filterCandMap(candMap, rowsExpr);

      if (debug >= 2)
      {
        for (auto &e : candMap[invDecl])
        {
          outs() << "  invs from data: " << e << "\n";
        }
      }
      return res;
    }

    Expr mutateInfer(Expr a, Expr b, bool first, ExprVector& BigPhi)
    {
      Expr opExpr = first ? a : b;
      Expr res = mk<TRUE>(m_efac);
      if(isOpX<GT>(opExpr)) res = mk<GT>(a->left(), b->left());
      if(isOpX<LT>(opExpr)) res = mk<LT>(a->left(), b->left());
      if(isOpX<GEQ>(opExpr)) res = mk<GEQ>(a->left(), b->left());
      if(isOpX<LEQ>(opExpr)) res = mk<LEQ>(a->left(), b->left());
      if(isOpX<EQ>(opExpr)) res = mk<EQ>(a->left(), b->left());
      if(isOpX<NEQ>(opExpr)) res = mk<NEQ>(a->left(), b->left());

      if(!u.isTrue(res) && u.isSat(res, firstRowExpr) && checkSanity(res, BigPhi)) return res; 
      return mk<TRUE>(m_efac);
    }

    bool checkSanity(Expr inferred, ExprVector& BigPhi)
    {
      ExprSet inf;
      inf.insert(inferred);
      return checkSanity(inf, BigPhi);
    }

    bool checkSanity(ExprSet& inferred, ExprVector& BigPhi)
    {
      for (auto &c : BigPhi)
      {
        if (u.implies(c, conjoin(inferred, m_efac)))
        {
          if(debug >= 7) outs() << "SANE\n";
        }
        else
        {
          if(debug >= 7) outs() << "INSANE\n";
          return false;
        }
      }
      return true;
    }

    void printBigPhi(ExprVector& BigPhi)
    {
      outs() << "  BigPhi size: " << BigPhi.size() << "\n";
      for (auto &c : BigPhi)
      {
        outs() << "  From BigPhi: " << c << std::endl;
        ;
      }
    }

    void mutateHeuristicInf(ExprSet& mutatedInferred, ExprSet& inferred, ExprVector& BigPhi)
    {
      for (auto &i : inferred)
      {
        for (auto &ii : inferred)
        {
          if (i == ii)
            continue;
          mutatedInferred.insert(mutateInfer(i, ii, true, BigPhi));
          mutatedInferred.insert(mutateInfer(i, ii, false, BigPhi));
          mutatedInferred.insert(mutateInfer(ii, i, true, BigPhi));
          mutatedInferred.insert(mutateInfer(ii, i, false, BigPhi));
        }
      }

      if (debug >= 4)
      {
        outs() << "  Mutated inferred:\n";
        for (auto &i : mutatedInferred)
        {
          outs() << "  " << i << "\n";
        }
      }
    }

    void adaptInterval(ExprSet& vars)
    {
      if(debug >= 4) outs() << "Testing interval\n================\n";

      vector<int> interval = {-10, 10};
      int upperBound = interval[1];
      int lowerBound = interval[0];

      if(debug >= 5)
      {
        outs() << "  upperBound: " << upperBound << "\n";
        outs() << "  lowerBound: " << lowerBound << "\n";
        outs() << "  specDecl: " << specDecl << "\n";
        outs() << "  invDecl: " << invDecl << "\n";
      } 

      candidates.clear();
      for(auto& v: vars)
      {
        candidates[invDecl].insert(mk<LEQ>(v, mkMPZ(upperBound, m_efac)));
        candidates[specDecl].insert(mk<LEQ>(replaceAll(v, tr->srcVars, fc->srcVars), 
                                            mkMPZ(upperBound, m_efac)));
      }

      for(auto& c: candidates[invDecl])
      {
        if(debug >= 5) outs() << "  c: " << c << "\n";
      }

      int mid = upperBound;
      int mid2 = lowerBound;

      while(mid != mid2)
      {
        mid2 = mid;

        vector<HornRuleExt*> worklist;
        worklist.push_back(fc);
        worklist.push_back(tr);
        worklist.push_back(qr);

        bool res = multiHoudini(worklist);

        mid = (mid + lowerBound) / 2;

        if (debug >= 5)
        {
          outs() << "After Houdini\n";
          outs() << "Houdini returned: " << res << "\n";
          outs() << "previous mid: " << mid2 << "\n";
          outs() << "mid: " << mid << "\n";
          for (auto &c : candidates[invDecl])
          {
              outs() << "  c: " << c << "\n";
          }
        }

        candidates.clear();
        for (auto &v : vars)
        {
          candidates[invDecl].insert(mk<LEQ>(v, mkMPZ(mid, m_efac)));
          candidates[specDecl].insert(mk<LEQ>(replaceAll(v, tr->srcVars, fc->srcVars),
                                              mkMPZ(mid, m_efac)));
        }
        if(!res) break;
      }

    }

    bool inferInequalities(ExprSet& ineqs, ExprVector& BigPhi)
    {
      ExprVector a;
      a.push_back(mkMPZ(-1, m_efac));
      a.push_back(mpzZero);
      a.push_back(mpzOne);

      ExprVector vars;
      for(auto& v: tr_nogh.srcVars)
      {
        vars.push_back(mk<MULT>(a[0], v));
        vars.push_back(mk<MULT>(a[1], v));
        vars.push_back(mk<MULT>(a[2], v));
      }

      if(debug >= 5)
      {
        for(auto& v: vars) 
          outs() << v << ", ";
        outs() << "\n\n";
      }

      ExprSet vars2;
      for(auto i = vars.begin(); i != vars.end(); i++)
      {
        for(auto j = vars.begin(); j != vars.end(); j++)
        {
          if((*i)->right() == (*j)->right()) 
          {
            continue;
          }
          Expr add = simplifyArithm(mk<PLUS>(*i, *j));
          if(add == mpzZero) continue;
          vars2.insert(add);
        }
      }

      if (debug >= 5)
      {
        for (auto &v : vars2)
          outs() << v << ", ";
        outs() << "\n\n";
      }

      ExprSet tmp; // Make combinations of LEQ GEQ here. Check for redundancy.
      for(auto& v: vars2)
      {
        tmp.insert(simplifyArithm(normalize(mk<LEQ>(v, mpzZero), mpzZero)));
        tmp.insert(simplifyArithm(normalize(mk<GEQ>(v, mpzZero), mpzZero)));
      }

      for(auto& t: tmp)
      {
        if(checkSanity(t, BigPhi))
        {
          Expr tt = normalize(t);
          if(isOpX<MULT>(tt->left()) && tt->right() == mpzZero)
          {
            tt = reBuildCmp(tt, tt->left()->right(), mpzZero);
          }
          if(toKeep(tt, 1))
            ineqs.insert(tt);
        } 
      }
      tmp.clear();
      for(auto& v: vars2)
      {
        for(auto& vv: vars2)
        {
          if(v == vv) continue;
          tmp.insert(normalize(normalize(simplifyArithm(mk<LEQ>(v, vv))), mpzZero));
          tmp.insert(normalize(normalize(simplifyArithm(mk<GEQ>(v, vv))), mpzZero));
        }
      }
      for (auto &t : tmp)
      {
        if (checkSanity(t, BigPhi))
        {
          Expr tt = normalize(t);
          if (isOpX<MULT>(tt->left()) && tt->right() == mpzZero)
          {
            tt = reBuildCmp(tt, tt->left()->right(), mpzZero);
          }
          if(toKeep(tt, 1))
            ineqs.insert(tt);
        }
      }
      if(debug >= 4)
      {
        outs() << "Inequalities\n";
        for(auto& i: ineqs)
        {
          outs() << i << "\n";
        }
      }
      return true;
    }

    Expr getNextMutant(ExprSet& mutatedInferred)
    {
      if(mutatedInferred.empty()) return mk<TRUE>(m_efac);
      Expr mutant = *mutatedInferred.begin();
      mutatedInferred.erase(mutatedInferred.begin());
      return mutant;
    }

    Expr weakenAndCheck(ExprSet& inferred, Expr mutant, Expr bound)
    {
      if(debug >= 2) outs() << "\n\nWeaken & Check\n==============\n";
      ExprSet tmpInf = inferred;
      ExprSet reAdd;

      while(!tmpInf.empty())
      {
        Expr check = *tmpInf.begin();
        tmpInf.erase(tmpInf.begin());

        Expr c = conjoin(tmpInf, m_efac);
        Expr m = mk<AND>(mutant, conjoin(reAdd, m_efac));
        c = mk<AND>(c, m);
        c = simplifyArithm(c);

        if(debug >= 2) outs() << "  c: " << c << "\n";
        if(debug >= 2) outs() << "  check: " << check << "\n";

        boost::tribool safe = checkSafety(c, bound);

        if(!safe)
        {
          if(debug >= 2) outs() << "Readding: " << check << "\n";
          reAdd.insert(check);
        }
        if(debug >= 2 && safe) outs() << "  Dropping" << check << "\n";
      }
      if(debug >= 2)
      {
        outs() << "\n\nreAdd: " << conjoin(reAdd, m_efac) << std::endl;
        outs() << "checking safety of: " << conjoin(reAdd, m_efac) << std::endl;
      }
      assert(checkSafety(mk<AND>(mutant, conjoin(reAdd, m_efac)), bound));
      inferred = reAdd;

      if(debug >= 2) outs() << "\n==============\n";
      return simplifyArithm(mk<AND>(conjoin(inferred, m_efac), mutant));
    }

    Expr inferFromProjs(ExprVector &BigPhi, Expr bound)
    {
      if(debug >= 2)
        outs() << "\n\nInfer From Projections\n==============\n";
      if(debug >= 4) printBigPhi(BigPhi);

      ExprSet inferred = infer(BigPhi); // Main routine here.
      if(!checkSanity(inferred, BigPhi)) return mk<FALSE>(m_efac);
      
      ExprSet mutatedInferred;
      if(mutateInferred) 
      {
        inferInequalities(mutatedInferred, BigPhi);
      }

      Expr c;
      boost::tribool safe = false; 

      do
      {
        Expr mutant = getNextMutant(mutatedInferred);

        c = conjoin(inferred, m_efac);
        c = mk<AND>(c, mutant);
        c = simplifyArithm(c);
        if(debug >= 2) outs() << "  c with mutated Expr: " << c << "\n";
        // try to weaken the precond iteratively and send back to FH only if safe.
        safe = checkSafety(c, bound);
        if(safe) {
          c = weakenAndCheck(inferred, mutant, bound);
          prevInvs.clear();
        } 
      } while (!safe && !mutatedInferred.empty());


      if(debug >= 3) 
      {
        if(!safe) outs() << "\n\n********\n*UNSAFE*\n********\n\n";
        else outs() << "\n\n******\n*SAFE*\n******\n\n";
      }

      if(!safe) return mk<FALSE>(m_efac);
      if(debug >= 3) outs() << "  Result from checkSafety: " << c << " => " << replaceAll(bound, fc->srcVars, tr->srcVars) << "\n";

      return c;
    }

    Expr abduction(Expr& phi, Expr& f, Expr& preCond, 
                int k, vector<ExprVector>& vars, vector<int>& trace,
                BndExpl& bnd, CHCs& rm)
    {
      trace.push_back(2); // Need to add the query to the trace.

      if(debug >= 2) outs() << "\nAbduction\n=========\n";

      phi = bnd.toExpr(trace);
      vars = bnd.getBindVars();
      for (auto v = vars.begin(); v != vars.end(); )
      {
        if (v->size() == 0) { v = vars.erase(v); }
        else { ++v; }
      }

      if(debug >= 3) 
      {
        outs() << "  k: " << k << "  vars size: " << vars[vars.size() - 1].size();
        outs() << "  invVars.size(): " << rm.invVars[invDecl].size() << "\n\n";
      }

      Expr ff = normalize(f, ghostVars[0]);
      Expr fg = mk<EQ>(ff->right(), ghostValue);

      if (debug >= 3)
      {
        outs() << "  ff: ";
        pprint(ff, 2);
        outs() << "  gh value: " << fg << "\n";
      }
      
      for (int i = 1; i < k; i++)
        fg = replaceAll(fg, vars[vars.size() - i - 1], vars[vars.size() - i]);
      
      fg = replaceAll(fg, rm.invVars[invDecl], vars[vars.size() - 1]);

      Expr lg = replaceAll(loopGuard, rm.invVars[invDecl], vars[vars.size() - 1]);
      if(debug >= 5) outs() << "  gh value (vars replaced): " << fg << "\n";

      phi = mk<AND>(phi, mk<AND>(fg,mkNeg(lg)));

      if(debug >= 4)
      {
        outs() << "  phi: ";
        pprint(phi,2);
      }

      ff = replaceAll(ff, tr->srcVars, fc->srcVars);
      preCond = ff;

      Expr elim;
      elim = eliminateQuantifiers(phi, vars[vars.size() - 1]);
      for (int i = 1; i < k; i++)
      {
        elim = eliminateQuantifiers(elim, vars[vars.size() - i - 1]);
      }

      return elim;
    }

    Expr makePretty(Expr elim, int k, vector<ExprVector>& vars, CHCs& rm)
    {
      Expr e = elim;
      for (int i = 1; i < k; i++)
      {
        e = replaceAll(e, vars[vars.size() - i - 1], vars[vars.size() - i]);
      }

      e = replaceAll(e, vars[0], rm.invVars[invDecl]);
      return e;
    }

    boost::tribool toKeep(Expr p, int k)
    {
      // If a projection (p) is satisfiable with one of the rows from data
      // keep it. Else throw it away.
      if (debug >= 4)
        outs() << "  Checking Projection: " << simplifyArithm(p) << "\n";

      for(int i = 0; i < k; i++)
      {
        if(debug >= 5) outs() << "  Checking row[" << i << "]: " << rowsExpr[i] << "\n";
        if(u.isSat(rowsExpr[i], p))
        {
          if(debug >= 5) outs() << "  Keeping\n";
          return true;
        } 
      }
      return false;
    }

    vector<ExprVector> abds;
    vector<ExprVector> allCombs;
    bool abdErr = false;
    Expr getPre(Expr p, Expr f, vector<int> m)
    {
      // p holds the conjunction of the negated previous preconditions.
      // f is the data invariant.
      // n is the number of iterations.
      // returns the precondition for the next iteration.

      if(debug >= 2) outs() << "\n\nGet Pre\n=======\n";

      if(debug >= 5)
      {
        outs() << "  p: ";
        pprint(p, 2);
        outs() << "  f: ";
        pprint(f, 2);
      }

      ExprSet Phi;
      CHCs rm(m_efac, z3, debug);

      vector<HornRuleExt*> rules;
      rules.push_back(&fc_nogh);
      rules.push_back(&tr_nogh);
      rules.push_back(&qr_nogh);
      prepareRuleManager(rm, rules);

      BndExpl bnd(rm, (debug > 0));
      Expr bound;

      abds.clear();
      allCombs.clear();
      for(auto k: m) 
      {
        vector<int> trace;
        buildTrace(trace, k);

        Expr phi = bnd.toExpr(trace);

        if (!u.isSat(phi))
        {
          Expr res = mk<TRUE>(m_efac);
          if(debug >= 4) outs() << "  phi is UNSAT in getPre\n";
          return res;
        }

        vector<ExprVector> vars;
        Expr elim = simplifyArithm(
          abduction(phi, f, bound, k, vars, trace, bnd, rm));

        // value of y = 1, y = 2, y = 4... make an example like this.
        
        if (u.implies(elim, phi))
        {
          if(debug >= 4) outs() << "  ERROR with abduction\n";
          abdErr = true;
          continue;
        }

        abdErr = false;
        elim = simplifyArithm(makePretty(elim, k, vars, rm));

        if (debug >= 3)
        {
          if(debug >= 4) outs() << "  bound: " << bound << "\n";
          outs() << "  Result from Abduction: ";
          pprint(elim, 2);
        }

        ExprVector prjcts, prjcts2;
        u.flatten(elim, prjcts2, false, invVars, keepQuantifiersRepl);

        for(auto& p: prjcts2)
        {
          if(debug >= 4) outs() << "  Projection: " << normalize(p) << "\n";
          if(checkProj)
          {
            if(toKeep(p, k)) // If enabled, checks the projection before adding it.
            {
              prjcts.push_back(simplifyArithm(p));
            }
          }
          else // If disabled, adds the projection without checking.
          {
            prjcts.push_back(simplifyArithm(p));
          }  
        }

        abds.push_back(prjcts);
      }

      if(abds.size() < 1) return mk<TRUE>(m_efac);

      if (debug >= 4) 
      {
        for (int i = 0; i < abds.size(); i++)
        {
          for (int j = 0; j < abds[i].size(); j++)
          {
            outs() << "  Final from Abduction " << i << ": " << abds[i][j] << "\n";
          }
        }
      }
      getAllCombs(allCombs, abds, 0);
      if(debug >= 4)
      {
        outs() << "  All Combs size: " << allCombs.size() << "\n";
        int i = 0;
        for(auto& c: allCombs)
        {
          for(auto& cc: c)
          {
            outs() << "Comb " << i << ": " << cc << "\n";
          }
          i++;
        }
      }
      Expr a = mk<FALSE>(m_efac);

      for(int i = 0; i < allCombs.size(); i++)
      {
        ExprVector current;
        for(int j = 0; j < allCombs[i].size(); j++)
        {
          current.push_back(allCombs[i][j]);
        }

        if(debug >= 3) 
        {
          outs() << "  projs[ " << i << " ]:\n";
          pprint(current);
          outs() << "\n\n";
        }
        Expr b = inferFromProjs(current, bound);
        if(debug >= 3) outs() << "  Result from W&S: " << b << "\n";
        if(u.implies(a, b)) a = b;
        else if(u.implies(b, a)) continue;
        else a = mk<OR>(a, b);

        if(debug >= 3) outs() << "Current a: " << a << "\n";
      }

      return a;
    }

    void getAllCombs(vector<ExprVector>& allCombs, vector<ExprVector>& abds, int i)
    {
      if(abds.empty()) return;  
      if(debug >= 5)
      {
        outs() << "  All Combs size: " << allCombs.size() << "\n";
        int i = 0;
        for(auto& c: allCombs)
        {
          for(auto& cc: c)
          {
            outs() << "Combs so far " << i << ": " << cc << "\n";
          }
          i++;
        }
      }      

      int j = abds[i].size();

      if(i == 0)
      {
        for(int d = 0; d < j; d++)
          allCombs.push_back({abds[i][d]});
      }
      else
      {
        vector<ExprVector> temp;

        for(int l = 0; l < j; l++)
        {
          for(int k = 0; k < allCombs.size(); k++)
          {
            temp.push_back(allCombs[k]);
          }
        }

        int jPrev = abds[i-1].size();
        int k = 0;
        for(int l = 0; l < temp.size(); l++)
        {
          if(l != 0 && l % jPrev == 0) k++;
          if(k >= abds[i].size()) break;
          temp[l].push_back(abds[i][k]);
        }
        
        allCombs = temp;
      } 


      if(i + 1 >= abds.size()) return;
      getAllCombs(allCombs, abds, i + 1);
    }

    Expr constructPhi(Expr& p)
    {
      p = mk<TRUE>(m_efac);
      for (auto &b : bounds)
      {
        Expr psi = b.first;
        psi = mk<AND>(p, mkNeg(psi));
        
        p = mk<AND>(p, psi);
      }

      p = simplifyArithm(p);

      Expr phi = mk<AND>(p, replaceAll(fc_nogh.body, invVarsPr, invVars), loopGuard);

      return phi;
    }

    void buildTrace(vector<int>& trace, int i, bool addQuery = false)
    {
      trace.push_back(0); // We know we have a single loop system.
      for (int k = 0; k < i; k++) trace.push_back(1);
      if (addQuery) trace.push_back(2);

      if(debug >= 4) 
      {
        outs() << "\n  Trace information: size: ";
        outs() << trace.size() << "\n  ";
        for (auto &t : trace)
          outs() << t << "  ";
        outs() << "\n";
      }
    }

    void solve()
    {
      // Implements Alg 1 and Alg 2 from the paper "Exact Loop Bound Analysis"
      
      if(debug) outs() << "\n\nSolve\n=====\n\n";
      if(debug >= 3) ruleManager.print(true);

      Expr prevPsi;

      while (true)
      {
        if(n > 100 * limit) return;

        Expr p;
        Expr phi = constructPhi(p);
        if(debug >= 2) 
        {
          outs() << "  phi: ";
          pprint(phi, 2);
        }

        if (!u.isSat(phi))
        {
          if(debug >= 3) outs() << "  phi is UNSAT\n";
          p = simplifyArithm(p);
          if(debug >= 4) outs() << "  Final p: " << p << "\n";
        
          if(debug >= 2) outs() << "  Adding zero bound.\n";
          if(!u.isFalse(p)) bounds[p] = mk<EQ>(ghostVars[0], mkMPZ(0, m_efac));
          return;
        }
        if(debug >= 4) outs() << "  phi is SAT\n";

        boost::tribool res;
        map<Expr, ExprSet> forms;
        Expr model;
        vector<int> m;
        for(int i = 0; i < n; i++)
        {
          vector<int> trace;
          BndExpl bnd(ruleManager, (debug > 0));

          buildTrace(trace, i+1, true);

          Expr ssa = bnd.toExpr(trace);
          ssa = mk<AND>(p, ssa);
          ssa = replaceAll(ssa, fc->srcVars, invVars);

          if(debug >= 4) {
            outs() << "SSA: ";
            pprint(ssa, 2);
          }
          
          if(u.isSat(ssa))
          {
            m.push_back(i+1);
            // update to use models for data learning.
            model = u.getModel();
            if (debug >= 5)
            {
              outs() << "  i: " << m.back() << "\n";
              outs() << "  Model: ";
              pprint(model, 2);
            } 

            // if(i > 5) break;
          }
          else if(debug >= 4) { outs() << "  ====  SSA is UNSAT\n"; }
        }

        ghostGuard = setGhostGuard(mkMPZ(0, m_efac));
        qr->body = mk<AND>(mkNeg(loopGuard), ghostGuard);

        bool nonterm = false;
        if(m.empty()) // this is a check to see if we have a nonterminating case.
        {
          ghostGuard = setGhostGuard(mkMPZ(-1,m_efac));
          qr->body = mk<AND>(loopGuard, ghostGuard);
          m.push_back(1);
          nonterm = true;
        }

        if(debug >= 4)
        {
          outs() << "  m: ";
          for(auto& i: m) outs() << i << " ";
          outs() << "\n";
        }
        res = invFromData(fc->body, qr->body, p, forms, m.back());
        
        if (res == true)
        {
          ExprSet invs;
          Expr psi;

          ExprVector formsVec;
          for (auto &s : forms[invDecl])
          {
            formsVec.push_back(s);
          }

          sortBounds(formsVec);

          if (debug >= 3)
          {
            outs() << "  ==> Sorted invs from data:\n";
            pprint(formsVec, 4);
          }

          for (auto &f : formsVec)
          {
            if (debug >= 3)
              outs() << "Trying next bound: " << f << "\n";
            bool toContinue = false;
            for (auto &b : bounds)
            {
              if (b.second == f)
              {
                if (debug >= 4)
                  outs() << "  Bound already found\n";
                toContinue = true;
              }
            }
            if (toContinue)
              continue;

            psi = getPre(p, f, m);
            psi = simplifyArithm(psi);
            if(debug >= 4) outs() << "  psi after getPre: " << psi << "\n";
            if (!abdErr && !isOpX<FALSE>(psi))
            {
              if (debug >= 2)
              {
                outs() << "\n---->  Adding bound:\n";
                pprint(psi);
                outs() << " => ";
                outs() << normalize(f, ghostVars[0]) << " 😎\n\n";
              }
              bounds[psi] = normalize(f, ghostVars[0]);
              break;
            }
          }
        }
        else
        {
          n++;
          if(debug >= 2) outs() << "  UNKNOWN\n";
          if(debug >= 3) outs() << "  n: " << n << "\n";
        }
        m.clear();
      }
    }

    void printResults(bool success = true)
    {
      if(!bounds.empty() && success) outs() << "\nSuccess! Found bounds:\n";
      else if(!success) outs() << "\nBounds so far:\n";
      // int i = 0;
      for (auto b = bounds.begin(); b != bounds.end(); b++)
      {
        outs() << b->first << " --> " << b->second;
        outs() << "\n";
      }
      outs() << "\n";
    }
  }; // End class BoundSolverV2

  inline void learnBoundsV2(string smt, int inv, int stren, bool dg,
                                  bool data2, bool doPhases, int limit, 
                                  bool gj, bool dc, bool ac, bool iwd, 
                                  bool imp, bool mi, bool so, bool tk,
                                  int md, int debug)
  {
    ExprFactory m_efac;
    EZ3 z3(m_efac);
    CHCs ruleManager(m_efac, z3, debug);

    ruleManager.parse(smt, false);

    BoundSolverV2 bs(ruleManager, inv, dg, data2, doPhases, limit, gj,
                     dc, ac, iwd, imp, mi, so, tk, md, debug);

    bs.setUpQueryAndSpec(mk<TRUE>(m_efac), mk<TRUE>(m_efac));

    bs.solve();
    bs.printResults();
  }
}

#endif // BOUND_SOLVER_V2_HPP
