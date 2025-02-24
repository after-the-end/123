import java.util.*;

import com.microsoft.z3.*;

class Nqueen {
    public static void main(String[] args) {
        try {
            HashMap<String, String> cfg = new HashMap<String, String>();
            cfg.put("model", "true");
            Context ctx = new Context(cfg);
            Scanner scan = new Scanner(System.in);
            int n = 0;
            n = scan.nextInt();
            IntExpr[][] X = new IntExpr[n][];
            for (int i = 0; i < n; ++i) {
                X[i] = new IntExpr[n];
                for (int j = 0; j < n; ++j)
                    X[i][j] = (IntExpr) ctx.mkConst(
                            ctx.mkSymbol("x_" + (i + 1) + "_" + (j + 1)),
                            ctx.getIntSort());
            }

            Solver solver = ctx.mkSolver();

            int num = 0;
            BoolExpr[] loc_c = new BoolExpr[n];
            while (scan.hasNextInt()) {
                int coord_x = scan.nextInt(), coord_y = scan.nextInt();
                loc_c[num] = ctx.mkEq(X[coord_x - 1][coord_y - 1], ctx.mkInt(1));
                solver.add(loc_c[num]);
                ++num;
            }

            BoolExpr[][] cells_c = new BoolExpr[n][];
            for (int i = 0; i < n; ++i) {
                cells_c[i] = new BoolExpr[n];
                for (int j = 0; j < n; ++j) {
                    cells_c[i][j] = ctx.mkAnd(ctx.mkLe(ctx.mkInt(0), X[i][j]), ctx.mkLe(X[i][j], ctx.mkInt(1)));
                }
            }
            for (BoolExpr[] t : cells_c)
                solver.add(t);

            BoolExpr[] row_c = new BoolExpr[n];
            ArithExpr[] row_sum = new ArithExpr[n];
            for (int i = 0; i < n; ++i) {
                row_sum[i] = ctx.mkInt(0);
                for (int j = 0; j < n; ++j) {
                    row_sum[i] = ctx.mkAdd(row_sum[i], X[i][j]);
                }
                row_c[i] = ctx.mkEq(row_sum[i], ctx.mkInt(1));
            }
            solver.add(row_c);

            BoolExpr[] col_c = new BoolExpr[n];
            ArithExpr[] col_sum = new ArithExpr[n];
            for (int j = 0; j < n; ++j) {
                col_sum[j] = ctx.mkInt(0);
                for (int i = 0; i < n; ++i) {
                    col_sum[j] = ctx.mkAdd(col_sum[j], X[i][j]);
                }
                col_c[j] = ctx.mkEq(col_sum[j], ctx.mkInt(1));
            }
            solver.add(col_c);

            BoolExpr[] dia_r_c = new BoolExpr[2 * n - 1];
            ArithExpr[] dia_r_sum = new ArithExpr[2 * n - 1];
            for (int i = 0; i < 2 * n - 1; ++i) {
                dia_r_sum[i] = ctx.mkInt(0);
                if (i < n) {
                    int coord_x = 0, coord_y = i;
                    for (int j = 0; coord_y + j < n; ++j) {
                        dia_r_sum[i] = ctx.mkAdd(dia_r_sum[i], X[coord_x + j][coord_y + j]);
                    }
                } else {
                    int coord_x = i - n + 1, coord_y = 0;
                    for (int j = 0; coord_x + j < n; ++j) {
                        dia_r_sum[i] = ctx.mkAdd(dia_r_sum[i], X[coord_x + j][coord_y + j]);
                    }
                }
                dia_r_c[i] = ctx.mkLe(dia_r_sum[i], ctx.mkInt(1));
            }
            solver.add(dia_r_c);

            BoolExpr[] dia_l_c = new BoolExpr[2 * n - 1];
            ArithExpr[] dia_l_sum = new ArithExpr[2 * n - 1];
            for (int i = 0; i < 2 * n - 1; ++i) {
                dia_l_sum[i] = ctx.mkInt(0);
                if (i < n) {
                    int coord_x = 0, coord_y = i;
                    for (int j = 0; coord_y + j < n; ++j) {
                        dia_l_sum[i] = ctx.mkAdd(dia_l_sum[i], X[coord_x + j][coord_y + j]);
                    }
                } else {
                    int coord_x = i - n + 1, coord_y = 0;
                    for (int j = 0; coord_x + j < n; ++j) {
                        dia_l_sum[i] = ctx.mkAdd(dia_l_sum[i], X[coord_x + j][coord_y + j]);
                    }
                }
                dia_l_c[i] = ctx.mkLe(dia_l_sum[i], ctx.mkInt(1));
            }
            solver.add(dia_l_c);
            int ans = 0;
            if (solver.check() == Status.SATISFIABLE) {
                ++ans;
                Model m = solver.getModel();
                Expr[][] R = new Expr[n][n];
                for (int i = 0; i < n; ++i) {
                    for (int j = 0; j < n; ++j) {
                        R[i][j] = m.evaluate(X[i][j], false);
                    }
                }
                BoolExpr past_ans = ctx.mkTrue();
                for (int i = 0; i < n; ++i) {
                    for (int j = 0; j < n; ++j) {
                        past_ans = ctx.mkAnd(past_ans, ctx.mkEq(R[i][j], X[i][j]));
                    }
                }
                past_ans = ctx.mkNot(past_ans);
                solver.add(past_ans);
                while (solver.check() == Status.SATISFIABLE) {
                    ++ans;
                    m = solver.getModel();
                    R = new Expr[n][n];
                    for (int i = 0; i < n; ++i) {
                        for (int j = 0; j < n; ++j) {
                            R[i][j] = m.evaluate(X[i][j], false);
                        }
                    }
                    past_ans = ctx.mkTrue();
                    for (int i = 0; i < n; ++i) {
                        for (int j = 0; j < n; ++j) {
                            past_ans = ctx.mkAnd(past_ans, ctx.mkEq(R[i][j], X[i][j]));
                        }
                    }
                    past_ans = ctx.mkNot(past_ans);
                    solver.add(past_ans);
                }
                System.out.println("The number of solutions is: " + ans);
                System.out.println("N queen solution:");
                for (int i = 0; i < n; ++i) {
                    for (int j = 0; j < n; ++j) {
                        System.out.print(" " + R[i][j]);
                    }
                    System.out.println();
                }
            } else {
                System.out.println("No solution");
            }
            String str1 = scan.nextLine();
            ctx.close();
        } catch (Z3Exception e) {
            e.printStackTrace();
        }
    }
}