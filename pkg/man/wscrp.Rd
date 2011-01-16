\name{wscrp}
\alias{wscrp}
\title{ Weighted Successive Constant Rebalanced Portfolio }
\description{
  Calculate current portfolio weights as a weighted average of the best
  CRP until now and the previous weights
}
\usage{
wscrp(x, from = 1, by = 1, alpha = 0.99, fast.only = TRUE)
}
\arguments{
  \item{x}{
    Time series of relative prices
}
\item{from}{
  Start index, can be different from 1 to avoid the very instable
  first periods.
}
  \item{by}{
    Step in time to recalculate best CRP
}
  \item{alpha}{
    The weight between old and new, should be in range [0,1], closer to
    1 means more filtering
}
\item{fast.only}{
  Only use the fast but slightly inaccurate version of CRP optimization
}
}
\details{
  At each time index ti = from + i * by, calculate the weights for the best CRP up to
  but not including ti, call that crp_i, calculate the weigthed sum of
  (1-alpha) * crp_i + alpha * w_i-1 = w_i, use w_i as portfolio weights until the next
  optimization point.  Return the time series of the corresponding
  portfolio wealth.  w_0 is the uniform weight vector.
}
\value{
  Return the time series of portfolio wealths.
}
\references{
  Gaivoronski, A and Stella, F (2000): Nonstationary Optimization Approach for Finding Universal Portfolios. Published in: Annals of Operations Research , Vol. 100, (2000): pp. 165-188.
}
\author{ Marc Delvaux }
