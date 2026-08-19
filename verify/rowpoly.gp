\\ Polynomial for row n of A188147 (walks with n points, i.e. n-1 steps,
\\ on a k X k board, summed over all starting positions).
\\ Method: the count from a cell depends only on its distances to the four
\\ board edges clipped at m = n-1 (locality), so group cells by clipped
\\ window (memoized), then interpolate the polynomial from three values
\\ k = 2m+1..2m+3, where it is guaranteed to be polynomial.
\\ Example: RowPoly(3) = 12*k^2 - 24*k + 8.

\\ walks with s more edges from (x,y) in box [1..w]x[1..h], avoiding set v
cnt(w, h, s, v, x, y) = {
  if(s==0, return(1));
  my(t=0, d=[[1,0],[-1,0],[0,1],[0,-1]]);
  for(i=1, 4,
    my(p=[x,y]+d[i]);
    if(p[1]>=1 && p[1]<=w && p[2]>=1 && p[2]<=h && !setsearch(v, p),
      t += cnt(w, h, s-1, setunion(v, Set([p])), p[1], p[2])));
  t;
}

\\ total count on the k X k board, cells grouped by clipped window;
\\ windows are normalized by the board symmetries before memoization
Arow(n, k) = {
  my(m=n-1, M=Map(), tot=0);
  for(x=1, k, for(y=1, k,
    my(lx=min(x-1,m), rx=min(k-x,m), ly=min(y-1,m), ry=min(k-y,m),
       key=vecsort([vecsort([lx,rx]), vecsort([ly,ry])]), c);
    if(!mapisdefined(M, key, &c),
      c = cnt(lx+rx+1, ly+ry+1, m, Set([[lx+1,ly+1]]), lx+1, ly+1);
      mapput(M, key, c));
    tot += c));
  tot;
}

\\ the polynomial in k for row n, valid for all k >= 2*n-1 (in fact for
\\ k beyond the smaller threshold stated in the row entries)
RowPoly(n) = {
  my(m=n-1);
  polinterpolate([2*m+1, 2*m+2, 2*m+3],
                 [Arow(n,2*m+1), Arow(n,2*m+2), Arow(n,2*m+3)], 'k);
}
