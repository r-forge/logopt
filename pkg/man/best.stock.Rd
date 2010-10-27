\name{best.stock}
\alias{best.stock}
\alias{worst.stock}
\title{ Show time evolution of best or worst stock }
\description{
  Time evolution of the stock with the best or worst terminal wealth.
}
\usage{
best.stock(x)
}
\usage{
worst.stock(x)
}
\arguments{
  \item{x}{
        Time series of relative prices
}
}
\details{
  Contrast to best.envelope or worst.evolution that shows the best or
  worst wealth at any time index, irrespective of the stock.
}
\value{
  Time series of the wealth for the stock with best or worst terminal wealth.
}

\author{ Marc Delvaux}