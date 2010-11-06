\name{wscrp}
\alias{wscrp}
\title{ Weighted Successive Constant Rebalanced Portfolio }
\description{
  Calculate current portfolio weights as a weighted average of the best
  CRP until now and the previous weights
}
\usage{
wscrp(x, start = 1, by = 1, alpha = 0.99, fast.only = TRUE)
}
\arguments{
  \item{x}{
    Time series of relative prices
}
\item{start}{
    Start time 
}
  \item{by}{
    Step in time to recalculate best CRP
}
  \item{alpha}{
    The weight between old and new
}
\item{fast.only}{
  Only use the fast but slightly inaccurate version of CRP optimization
}
}
\details{
  At each time index ti = start + i * by, calculate the weights for the best CRP up to
  but not including ti, call that crp_i, calculate the weigthed sum of
  (1-alpha) * crp_i + alpha * w_i-1 = w_i, use w_i as weights the that as portfolio until the next
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
